/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Meta
import Lean.Meta.Sorry
import Lean.Elab.Term
import Lean.Compiler.ImplementedByAttr

public meta import Lean.Elab.Term.TermElabM

import Strata.Languages.Boole.Verify
import Strata.Transform.LoopElim

open Lean Meta Elab Term

---------------------------------------------------------------------

namespace Strata

/--
Convert a `Strata.Program` to a `Core.Program`, handling Boole and Core dialects.
Applies loop elimination so the resulting program contains no loop statements.
-/
def toCoreProgram (program : Strata.Program) : Option Core.Program := do
  if program.dialect == "Boole" then
    let booleProgram ← (Boole.getProgram program).toOption
    let coreProgram ← (Boole.toCoreProgram booleProgram program.globalContext).toOption
    return (Core.loopElim coreProgram).fst
  else if program.dialect == "Core" then
    let (p, #[]) := TransM.run default (translateProgram program) | none
    return (Core.loopElim p).fst
  else
    none

/--
Convert a `Strata.Program` to a `Core.Program` without loop elimination.
Used by `extract_def` so that loops are preserved for semantic extraction rather
than replaced by the verification-only assert/assume/havoc encoding.
-/
def toCoreProgramForExtract (program : Strata.Program) : Option Core.Program := do
  if program.dialect == "Boole" then
    let booleProgram ← (Boole.getProgram program).toOption
    (Boole.toCoreProgram booleProgram program.globalContext).toOption
  else if program.dialect == "Core" then
    let (p, #[]) := TransM.run default (translateProgram program) | none
    return p
  else
    none

namespace LeanExtract

/-- A symbolic store mapping variable names to their current Lean-expression values. -/
abbrev Store := Std.HashMap String Lean.Expr

/-- Context threaded through extraction: the program, a map from user-defined type names
to their Lean type expressions, and an optional self-reference for recursive procedures. -/
structure ExtractCtx where
  program  : Core.Program
  /-- Maps Boole datatype name (e.g. `"List"`) to its Lean type expr (e.g. `List Int`). -/
  typeMap  : Std.HashMap String Lean.Expr := {}
  /-- Maps Boole op names (constructors, testers, destructors) to the Lean function
      expressions that implement them for the user-annotated Lean types. -/
  opMap    : Std.HashMap String Lean.Expr := {}
  /-- When extracting a recursive procedure, holds `(procName, selfExpr)` so that
      recursive calls are replaced by applications of the partial def being built. -/
  selfProc : Option (String × Lean.Expr) := none
  /-- For structural recursion: maps each recursive field's FVarId to the corresponding
      inductive-hypothesis free variable.  Non-empty only during `buildStructuralCase`. -/
  structRecResults : Std.HashMap FVarId Lean.Expr := {}

/-- Check whether a procedure's body contains a self-recursive call. -/
private partial def hasSelfCall (procName : String) (stmts : List Core.Statement) : Bool :=
  stmts.any fun
    | .cmd (.call n _ _)  => n == procName
    | .ite _ t e _        => hasSelfCall procName t || hasSelfCall procName e
    | .block _ body _     => hasSelfCall procName body
    | _                   => false

/-- Translate a monomorphic Core type using a raw typeMap (used during context construction
    before an `ExtractCtx` exists). -/
private def translateTyWithMap (typeMap : Std.HashMap String Lean.Expr) : Lambda.LMonoTy → MetaM Lean.Expr
  | .tcons "int" []          => return .const ``Int []
  | .tcons "bool" []         => return .const ``Bool []
  | .tcons "Sequence" [elem] => do
      let e ← translateTyWithMap typeMap elem; Meta.mkAppM ``List #[e]
  | .bitvec n                => return mkApp (.const ``BitVec []) (mkNatLit n)
  | .tcons name [] =>
      match typeMap[name]? with
      | some ty => return ty
      | none    => throwError s!"extract_def: unknown type '{name}'"
  | ty => throwError s!"extract_def: unsupported type {repr ty}"

/-- Decompose a Lean arrow type into its argument types and final return type. -/
private def decomposeArrowType (ty : Lean.Expr) : List Lean.Expr × Lean.Expr :=
  match ty with
  | .forallE _ argTy body _ =>
    let (args, ret) := decomposeArrowType body
    (argTy :: args, ret)
  | _ => ([], ty)

/-- Record that a Boole type name maps to a Lean type expression.
    Built-in types (`int`, `bool`, `Sequence`) are left to `translateTy`. -/
private def matchBooleToLean (typeMap : Std.HashMap String Lean.Expr)
    (booleTy : Lambda.LMonoTy) (leanTy : Lean.Expr) : Std.HashMap String Lean.Expr :=
  match booleTy with
  | .tcons name [] =>
    if name == "int" || name == "bool" || name == "Sequence" then typeMap
    else typeMap.insert name leanTy
  | .bitvec _ => typeMap  -- built-in; mapped directly by translateTy
  | _ => typeMap

/-- Build a tester lambda `fun x => T.casesOn (fun _ => Bool) x case₀ … caseₙ`
    where only branch `j` returns `true`, all others `false`.
    `numParams` is the number of type-parameter implicit args before `motive` in `T.casesOn`. -/
private def buildTesterFun (leanTy : Lean.Expr) (indName : Name) (numParams : Nat)
    (booleConstrs : List (Lambda.LConstr Unit)) (j : Nat)
    (typeMap : Std.HashMap String Lean.Expr) : MetaM Lean.Expr := do
  let motive := Lean.Expr.lam `_ leanTy (.const ``Bool []) .default
  let indexed := (List.range booleConstrs.length).zip booleConstrs
  let cases ← indexed.mapM fun (i, constr) => do
    let result := if i == j then .const ``true [] else .const ``false []
    constr.args.foldrM (fun (_, fieldTy) acc => do
      let fTy ← translateTyWithMap typeMap fieldTy
      return Lean.Expr.lam `_ fTy acc .default) result
  Meta.withLocalDecl `x .default leanTy fun x => do
    let nones   := (List.replicate numParams (none : Option Lean.Expr)).toArray
    let optArgs := nones ++ #[some motive, some x] ++ cases.toArray.map some
    let app ← Meta.mkAppOptM (Name.str indName "casesOn") optArgs
    Meta.mkLambdaFVars #[x] app

/-- Build a destructor lambda `fun x => T.casesOn (fun _ => fieldTy) x default₀ … extractor_j … defaultₙ`
    where branch `ctorIdx` extracts field `fieldIdx` and all other branches return
    `Inhabited.default` for `fieldType`. -/
private def buildDestructorFun (leanTy : Lean.Expr) (indName : Name) (numParams : Nat)
    (booleConstrs : List (Lambda.LConstr Unit)) (ctorIdx fieldIdx : Nat)
    (fieldType : Lean.Expr) (typeMap : Std.HashMap String Lean.Expr) : MetaM Lean.Expr := do
  let motive  := Lean.Expr.lam `_ leanTy fieldType .default
  let u_inh   ← Meta.getLevel fieldType
  let inhInst ← Meta.synthInstance (.app (.const ``Inhabited [u_inh]) fieldType)
  let defVal  ← Meta.mkAppOptM ``default #[some fieldType, some inhInst]
  let indexed := (List.range booleConstrs.length).zip booleConstrs
  let cases ← indexed.mapM fun (i, constr) => do
    if i == ctorIdx then
      let fieldTys ← constr.args.mapM fun (_, ty) => translateTyWithMap typeMap ty
      let decls := (fieldTys.mapIdx fun k ty =>
        (Name.mkSimple s!"_f{k}", BinderInfo.default, fun _ : Array Lean.Expr => pure ty)).toArray
      Meta.withLocalDecls decls fun fvars => Meta.mkLambdaFVars fvars fvars[fieldIdx]!
    else
      constr.args.foldrM (fun (_, ty) acc => do
        let fTy ← translateTyWithMap typeMap ty
        return Lean.Expr.lam `_ fTy acc .default) defVal
  Meta.withLocalDecl `x .default leanTy fun x => do
    let nones   := (List.replicate numParams (none : Option Lean.Expr)).toArray
    let optArgs := nones ++ #[some motive, some x] ++ cases.toArray.map some
    let app ← Meta.mkAppOptM (Name.str indName "casesOn") optArgs
    Meta.mkLambdaFVars #[x] app

/-- Given a Boole `LDatatype` and the Lean type it maps to, look up the Lean inductive's
    constructors, then build opMap entries for all constructors, testers, and destructors. -/
private def buildOpMapForIndType (dt : Lambda.LDatatype Unit) (leanTy : Lean.Expr)
    (typeMap : Std.HashMap String Lean.Expr) : MetaM (Std.HashMap String Lean.Expr) := do
  let some indName := leanTy.getAppFn.constName?
    | throwError s!"extract_def: Lean type for '{dt.name}' is not an inductive"
  let env ← getEnv
  let some constInfo := env.find? indName
    | throwError s!"extract_def: '{indName}' not found in the Lean environment"
  let .inductInfo indInfo := constInfo
    | throwError s!"extract_def: '{indName}' is not an inductive type in the Lean environment"
  let numParams     := indInfo.numParams
  let typeArgs      := leanTy.getAppArgs       -- e.g. #[Int] for List Int
  let booleConstrs  := dt.constrs              -- List (LConstr Unit)
  let leanCtorNames := indInfo.ctors           -- List Name (in constructor order)
  unless booleConstrs.length == leanCtorNames.length do
    throwError s!"extract_def: constructor count mismatch for '{dt.name}' \
        (Boole: {booleConstrs.length}, Lean '{indName}': {leanCtorNames.length})"
  let mut opMap : Std.HashMap String Lean.Expr := {}
  let mut ctorIdx := 0
  for (booleConstr, leanCtorName) in booleConstrs.zip leanCtorNames do
    -- Constructor: partially apply the Lean constructor to any type arguments.
    let ctorExpr ← Meta.mkAppOptM leanCtorName (typeArgs.map some)
    opMap := opMap.insert booleConstr.name.name ctorExpr
    -- Tester.
    let testerExpr ← buildTesterFun leanTy indName numParams booleConstrs ctorIdx typeMap
    opMap := opMap.insert booleConstr.testerName testerExpr
    -- Destructors (safe and unsafe share the same Lean implementation).
    let mut fieldIdx := 0
    for (fieldId, fieldTy) in booleConstr.args do
      let leanFieldTy ← translateTyWithMap typeMap fieldTy
      let destrExpr ← buildDestructorFun leanTy indName numParams booleConstrs ctorIdx fieldIdx leanFieldTy typeMap
      opMap := opMap.insert s!"{dt.name}..{fieldId.name}"  destrExpr
      opMap := opMap.insert s!"{dt.name}..{fieldId.name}!" destrExpr
      fieldIdx := fieldIdx + 1
    ctorIdx := ctorIdx + 1
  return opMap

/-- Build `typeMap` and `opMap` by matching the procedure's Boole parameter types against
    the Lean types from the user's expected-type annotation.  Unknown ops in procedures that
    use only `int`/`bool` work fine with empty maps; user-defined types require the annotation. -/
def buildContextMaps (program : Core.Program) (proc : Core.Procedure)
    (expectedType : Option Lean.Expr)
    : MetaM (Std.HashMap String Lean.Expr × Std.HashMap String Lean.Expr) := do
  let mut typeMap : Std.HashMap String Lean.Expr := {}
  -- If the user supplied a type annotation, use it to derive Boole→Lean type mappings.
  if let some expTy := expectedType then
    let expTy ← instantiateMVars expTy
    let (leanArgTys, leanRetTy) := decomposeArrowType expTy
    let booleArgTys := proc.header.inputs.toList.map (·.2)
    for (b, l) in booleArgTys.zip leanArgTys do
      typeMap := matchBooleToLean typeMap b l
    if let some booleRetTy := proc.header.outputs.toList[0]?.map (·.2) then
      typeMap := matchBooleToLean typeMap booleRetTy leanRetTy
  -- For each user-defined type in typeMap, build its opMap entries.
  let mut opMap : Std.HashMap String Lean.Expr := {}
  for (booleTyName, leanTy) in typeMap.toList do
    let mDt := program.decls.findSome? fun d =>
      match d.getTypeDecl? with
      | some (.data block) => block.find? (·.name == booleTyName)
      | _ => none
    if let some dt := mDt then
      let newOps ← buildOpMapForIndType dt leanTy typeMap
      for (k, v) in newOps.toList do
        opMap := opMap.insert k v
  return (typeMap, opMap)

/-- Translate a monomorphic Core type to a Lean type expression. -/
def translateTy (ctx : ExtractCtx) : Lambda.LMonoTy → MetaM Lean.Expr
  | .tcons "int" []           => return .const ``Int []
  | .tcons "bool" []          => return .const ``Bool []
  | .tcons "Sequence" [elem]  => do
    let leanElem ← translateTy ctx elem
    Meta.mkAppM ``List #[leanElem]
  | .bitvec n                 => return mkApp (.const ``BitVec []) (mkNatLit n)
  | .tcons name [] =>
    match ctx.typeMap[name]? with
    | some ty => return ty
    | none    => throwError s!"extract_def: unsupported type '{name}'"
  | ty => throwError s!"extract_def: unsupported type {repr ty}"

/--
Build a `Bool`-branched if-then-else Lean expression.
Emits `Bool.casesOn cond falseCase trueCase`.
-/
def boolIteM (cond trueCase falseCase : Lean.Expr) : MetaM Lean.Expr := do
  let ty    ← Meta.inferType trueCase
  let level ← Meta.getLevel ty
  let motive := Lean.Expr.lam `b (.const ``Bool []) ty .default
  return mkApp4 (.const ``Bool.casesOn [level]) motive cond falseCase trueCase

/-- Wrap a Prop-valued expression in `decide` to get a `Bool`. -/
private def decideExpr (prop : Lean.Expr) : MetaM Lean.Expr := do
  let decInst ← Meta.synthInstance (.app (.const ``Decidable []) prop)
  return mkApp2 (.const ``decide []) prop decInst

/-- Apply a binary Core operator to two translated Lean expressions. -/
private def applyBinOp (ctx : ExtractCtx) (opName : String) (e1 e2 : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  | "Int.Add" => Meta.mkAppM ``HAdd.hAdd #[e1, e2]
  | "Int.Sub" => Meta.mkAppM ``HSub.hSub #[e1, e2]
  | "Int.Mul" => Meta.mkAppM ``HMul.hMul #[e1, e2]
  | "Int.Div" | "Int.DivT"   => Meta.mkAppM ``HDiv.hDiv #[e1, e2]
  | "Int.Mod" | "Int.ModT"   => Meta.mkAppM ``HMod.hMod #[e1, e2]
  | "Int.Lt" => decideExpr (← Meta.mkAppM ``LT.lt #[e1, e2])
  | "Int.Le" => decideExpr (← Meta.mkAppM ``LE.le #[e1, e2])
  | "Int.Gt" => decideExpr (← Meta.mkAppM ``GT.gt #[e1, e2])
  | "Int.Ge" => decideExpr (← Meta.mkAppM ``GE.ge #[e1, e2])
  | "Bool.And"     => return mkApp2 (.const ``Bool.and []) e1 e2
  | "Bool.Or"      => return mkApp2 (.const ``Bool.or []) e1 e2
  | "Bool.Implies" => return mkApp2 (.const ``Bool.or [])
                               (mkApp (.const ``Bool.not []) e1) e2
  | "Bool.Equiv"   => decideExpr (← Meta.mkAppM ``Eq #[e1, e2])
  | "Sequence.append"   => Meta.mkAppM ``List.append #[e1, e2]
  | "Sequence.build"    => Meta.mkAppM ``List.concat #[e1, e2]
  | "Sequence.take"     => do
    let n ← Meta.mkAppM ``Int.toNat #[e2]
    Meta.mkAppM ``List.take #[n, e1]
  | "Sequence.drop"     => do
    let n ← Meta.mkAppM ``Int.toNat #[e2]
    Meta.mkAppM ``List.drop #[n, e1]
  | "Sequence.select"   => do
    let i    ← Meta.mkAppM ``Int.toNat #[e2]
    let listTy ← Meta.inferType e1
    let elemTy := listTy.appArg!
    let u      ← Meta.getLevel elemTy
    let inst   ← Meta.synthInstance (.app (.const ``Inhabited [u]) elemTy)
    let dflt   ← Meta.mkAppOptM ``default #[some elemTy, some inst]
    Meta.mkAppM ``List.getD #[e1, i, dflt]
  | "Sequence.contains" => Meta.mkAppM ``List.elem #[e2, e1]
  | opName =>
    -- Bitvector ops: "Bv{n}.{kind}" (e.g. "Bv8.Xor", "Bv8.Add")
    if opName.startsWith "Bv" then
      let kind := (opName.splitOn ".").getLast?.getD ""
      match kind with
      | "Xor" => Meta.mkAppM ``HXor.hXor #[e1, e2]
      | "And" => Meta.mkAppM ``HAnd.hAnd #[e1, e2]
      | "Or"  => Meta.mkAppM ``HOr.hOr  #[e1, e2]
      | "Add" => Meta.mkAppM ``HAdd.hAdd #[e1, e2]
      | "Sub" => Meta.mkAppM ``HSub.hSub #[e1, e2]
      | "Mul" => Meta.mkAppM ``HMul.hMul #[e1, e2]
      | _ =>
        match ctx.opMap[opName]? with
        | some f => return mkApp2 f e1 e2
        | none   => throwError s!"extract_def: unsupported bitvector binary op '{opName}'"
    else
      match ctx.opMap[opName]? with
      | some f => return mkApp2 f e1 e2
      | none   => throwError s!"extract_def: unsupported binary op '{opName}'"

/-- Apply a unary Core operator to a translated Lean expression. -/
private def applyUnaryOp (ctx : ExtractCtx) (opName : String) (e : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  | "Int.Neg"         => Meta.mkAppM ``Neg.neg #[e]
  | "Bool.Not"        => return mkApp (.const ``Bool.not []) e
  | "Sequence.length" => do
    let n ← Meta.mkAppM ``List.length #[e]
    Meta.mkAppM ``Int.ofNat #[n]
  | op =>
    match ctx.opMap[op]? with
    | some f => return mkApp f e
    | none   => throwError s!"extract_def: unsupported unary op '{op}'"

/-- Apply a ternary Core operator to three translated Lean expressions. -/
private def applyTernaryOp (_ : ExtractCtx) (opName : String) (e1 e2 e3 : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  | "Sequence.update" => do
    let i ← Meta.mkAppM ``Int.toNat #[e2]
    Meta.mkAppM ``List.set #[e1, i, e3]
  | _ => throwError s!"extract_def: unsupported ternary op '{opName}'"

/-- Translate a Core expression to a Lean expression given a symbolic store. -/
partial def translateExpr (ctx : ExtractCtx) (store : Store) : Core.Expression.Expr → MetaM Lean.Expr
  | .const () (.intConst i) => return toExpr i
  | .const () (.boolConst b) => return toExpr b
  | .const () (.strConst _)
  | .const () (.realConst _) =>
    throwError "extract_def: real/string constants are not supported"
  | .const () (.bitvecConst n b) =>
    return mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit n) (mkNatLit b.toNat)
  | .fvar () id _ =>
    match store[id.name]? with
    | some e => return e
    | none   => throwError s!"extract_def: variable '{id.name}' not in store"
  | .ite () c t e => do
    let c' ← translateExpr ctx store c
    let t' ← translateExpr ctx store t
    let e' ← translateExpr ctx store e
    boolIteM c' t' e'
  | .eq () e1 e2 => do
    let e1' ← translateExpr ctx store e1
    let e2' ← translateExpr ctx store e2
    decideExpr (← Meta.mkAppM ``Eq #[e1', e2'])
  -- Ternary application: ((op e1) e2) e3
  | .app () (.app () (.app () (.op () id _) e1) e2) e3 => do
    let e1' ← translateExpr ctx store e1
    let e2' ← translateExpr ctx store e2
    let e3' ← translateExpr ctx store e3
    applyTernaryOp ctx id.name e1' e2' e3'
  -- Binary application: (op e1) e2
  | .app () (.app () (.op () id _) e1) e2 => do
    let e1' ← translateExpr ctx store e1
    let e2' ← translateExpr ctx store e2
    applyBinOp ctx id.name e1' e2'
  -- Unary application: op e
  | .app () (.op () id _) e => do
    let e' ← translateExpr ctx store e
    applyUnaryOp ctx id.name e'
  | .app () _ _ =>
    throwError "extract_def: unsupported application form in expression"
  -- Nullary ops: Sequence.empty and user-defined constructors (via opMap)
  | .op () id opTy =>
    match id.name with
    | "Sequence.empty" =>
      match opTy with
      | some (.tcons "Sequence" [elemTy]) => do
        let leanElem ← translateTy ctx elemTy
        Meta.mkAppOptM ``List.nil #[some leanElem]
      | _ => throwError "extract_def: Sequence.empty without a Sequence return type"
    | name =>
      match ctx.opMap[name]? with
      | some e => return e
      | none   => throwError s!"extract_def: bare op '{name}' not found in opMap"
  | .bvar () i =>
    throwError s!"extract_def: unexpected bound variable at index {i}"
  | .abs () _ _ _ =>
    throwError "extract_def: lambda abstractions in procedure bodies are not supported"
  | .quant () _ _ _ _ _ =>
    throwError "extract_def: quantifiers in procedure bodies are not supported"

/-- Merge two branch stores after an if/else, producing conditional expressions for differing keys. -/
private def mergeStores (cond : Lean.Expr) (baseStore storeT storeF : Store) : MetaM Store := do
  let allKeys := (storeT.toList ++ storeF.toList).map Prod.fst
  let mut merged := baseStore
  let placeholder := Lean.Expr.const ``True []
  for key in allKeys do
    let tVal := storeT[key]? |>.getD (baseStore[key]? |>.getD placeholder)
    let fVal := storeF[key]? |>.getD (baseStore[key]? |>.getD placeholder)
    if tVal == fVal then
      merged := merged.insert key tVal
    else
      merged := merged.insert key (← boolIteM cond tVal fVal)
  return merged

/-- Try to extract the counter variable from a for-loop body.
    Returns `(counterName, bodyWithoutStep)` if the last statement is
    `counter := counter + 1` (or `counter := counter + stepLiteral`). -/
private def extractCounterFromBody (body : List Core.Statement)
    : Option (String × List Core.Statement) :=
  match body.getLast? with
  | some (.cmd (.cmd (.set cid (.det
      (.app () (.app () (.op () addId _) (.fvar () fid _)) (.const () (.intConst stepN)))) _))) =>
    if addId.name == "Int.Add" && cid.name == fid.name && stepN == 1 then
      some (cid.name, body.dropLast)
    else none
  | _ => none

/-- Extract `(limitExpr, exclusive)` from a counting loop guard.
    Returns `some (limit, false)` for `counter <= limit` (inclusive upper bound),
    `some (limit, true)` for `counter < limit` (exclusive upper bound). -/
private def extractCountingBound (guard : Core.Expression.Expr) (counterName : String)
    : Option (Core.Expression.Expr × Bool) :=
  match guard with
  | .app () (.app () (.op () opId _) (.fvar () cid _)) limitExpr =>
    if cid.name == counterName then
      if opId.name == "Int.Le" then some (limitExpr, false)
      else if opId.name == "Int.Lt" then some (limitExpr, true)
      else none
    else none
  | _ => none

/-- Symbolically execute a list of Core statements, threading the store through. -/
partial def executeStmts (ctx : ExtractCtx) (store : Store) (stmts : List Core.Statement) : MetaM Store :=
  stmts.foldlM (executeStmt ctx) store
where
  /-- Inline a call to `procName` given the current store and call argument list. -/
  translateCall (ctx : ExtractCtx) (store : Store) (procName : String)
      (callArgs : List (Core.CallArg Core.Expression)) : MetaM Store := do
    let inputExprs := Core.CallArg.getInputExprs callArgs
    let translatedInputs ← inputExprs.mapM (translateExpr ctx store)
    let lhsVars := Core.CallArg.getLhs callArgs
    -- If this is a recursive self-call, resolve via structural IH or the opaque ref
    if let some (selfName, selfExpr) := ctx.selfProc then
      if procName == selfName then
        unless lhsVars.length == 1 do
          throwError s!"extract_def: recursive call to '{procName}' must have exactly 1 output"
        if !ctx.structRecResults.isEmpty then
          -- Structural mode: whnf the first argument to reach the field free variable,
          -- look up the pre-bound IH, then apply it to any extra arguments.
          unless translatedInputs.length >= 1 do
            throwError s!"extract_def: structural recursive call needs at least 1 argument"
          let arg ← Meta.whnf translatedInputs[0]!
          let .fvar fid := arg
            | throwError s!"extract_def: structural recursive call argument did not \
                reduce to a field variable (got {repr arg})"
          let some ihExpr := ctx.structRecResults[fid]?
            | throwError s!"extract_def: structural recursive call on unrecognized field FVar"
          -- Apply the IH to any extra arguments (inputs after the structural parameter).
          let result := (translatedInputs.drop 1).foldl Lean.mkApp ihExpr
          return store.insert lhsVars[0]!.name result
        else
          let recApp := translatedInputs.foldl Lean.mkApp selfExpr
          return store.insert lhsVars[0]!.name recApp
    -- Non-recursive case: inline the callee
    let some callee := Core.Program.Procedure.find? ctx.program procName
      | throwError s!"extract_def: called procedure '{procName}' not found"
    let calleeInputList := callee.header.inputs.toList
    unless calleeInputList.length == translatedInputs.length do
      throwError s!"extract_def: argument count mismatch calling '{procName}' \
          (expected {calleeInputList.length}, got {translatedInputs.length})"
    let calleeStore := (calleeInputList.zip translatedInputs).foldl
      (fun s ((id, _), e) => s.insert id.name e) {}
    let calleeFinalStore ← executeStmts ctx calleeStore callee.body
    let calleeOutputList := callee.header.outputs.toList
    unless calleeOutputList.length == lhsVars.length do
      throwError s!"extract_def: output count mismatch calling '{procName}' \
          (expected {calleeOutputList.length}, got {lhsVars.length})"
    let mut updatedStore := store
    for ((outId, _), lhsId) in calleeOutputList.zip lhsVars do
      let some outVal := calleeFinalStore[outId.name]?
        | throwError s!"extract_def: output '{outId.name}' was not assigned by '{procName}'"
      updatedStore := updatedStore.insert lhsId.name outVal
    return updatedStore
  /-- Symbolically execute one Core statement. -/
  executeStmt (ctx : ExtractCtx) (store : Store) (stmt : Core.Statement) : MetaM Store := do
    match stmt with
    | .cmd (.cmd (.set id (.det e) _)) =>
      return store.insert id.name (← translateExpr ctx store e)
    | .cmd (.cmd (.init id ty (.det e) _)) => do
      -- Boole `var x : T;` lowers to `init x := fvar("init_x_N")` with a fresh fvar not in
      -- the store — treat that pattern as havoc.
      match e with
      | .fvar () freshId _ =>
        if store.contains freshId.name then
          return store.insert id.name (← translateExpr ctx store e)
        else
          let .forAll _ mty := ty
          let leanTy ← try translateTy ctx mty catch _ => pure (Lean.mkConst ``Int)
          let mv ← Meta.mkFreshExprMVar leanTy
          return store.insert id.name mv
      | _ =>
        return store.insert id.name (← translateExpr ctx store e)
    | .cmd (.cmd (.set id .nondet _)) => do
      let mv ← Meta.mkFreshExprMVar (Lean.mkConst ``Int)
      return store.insert id.name mv
    | .cmd (.cmd (.init id ty .nondet _)) => do
      let .forAll _ mty := ty
      let leanTy ← try translateTy ctx mty catch _ => pure (Lean.mkConst ``Int)
      let mv ← Meta.mkFreshExprMVar leanTy
      return store.insert id.name mv
    | .cmd (.cmd (.assert _ _ _))
    | .cmd (.cmd (.assume _ _ _))
    | .cmd (.cmd (.cover  _ _ _)) => return store
    | .cmd (.call procName callArgs _) =>
      translateCall ctx store procName callArgs
    | .ite (.det condE) trueBranch falseBranch _ => do
      let condExpr ← translateExpr ctx store condE
      -- Short-circuit if the condition reduces to a Bool literal (e.g., a tester applied to
      -- a known constructor in structural-recursion mode).  This avoids executing unreachable
      -- branches that could contain unresolvable recursive calls.
      let condWhnf ← Meta.whnf condExpr
      if condWhnf == .const ``true [] then
        return ← executeStmts ctx store trueBranch
      else if condWhnf == .const ``false [] then
        return ← executeStmts ctx store falseBranch
      let storeT   ← executeStmts ctx store trueBranch
      let storeF   ← executeStmts ctx store falseBranch
      mergeStores condExpr store storeT storeF
    | .ite .nondet _ _ _ =>
      throwError "extract_def: nondeterministic branch conditions are not supported"
    | .block _ body _ => executeStmts ctx store body
    | .loop (.det guardE) _ _ body _ =>
      executeCountingLoop ctx store guardE body
    | .loop .nondet _ _ _ _ =>
      throwError "extract_def: nondeterministic loop guards are not supported"
    | .exit _ _ => return store
    | .funcDecl _ _ => return store
    | .typeDecl _ _ => return store
  /-- Execute a counting for-loop (`for i := lo to hi`) as a `List.foldl` over `List.range`.
      Recognises the pattern where the body ends with `counter := counter + 1`, computes
      the trip count from the guard (`counter <= hi` or `counter < hi`), and folds over
      the single accumulator variable modified by the loop body. -/
  executeCountingLoop (ctx : ExtractCtx) (store : Store)
      (guardE : Core.Expression.Expr) (body : List Core.Statement) : MetaM Store := do
    -- Detect counter: the last body statement must be `counter := counter + 1`.
    let some (counterName, bodyNoStep) := extractCounterFromBody body
      | throwError "extract_def: loop body must end with a +1 counter increment \
            (e.g. `i := i + 1`)"
    -- The counter must already be in the store (set by the `init` before the loop).
    let some counterInit := store[counterName]?
      | throwError s!"extract_def: loop counter '{counterName}' not initialised in store"
    -- Extract the upper bound from the guard.
    let some (limitCoreExpr, exclusive) := extractCountingBound guardE counterName
      | throwError "extract_def: loop guard must be 'counter <= limit' or 'counter < limit'"
    let limitLean ← translateExpr ctx store limitCoreExpr
    -- Compute the trip count as a `Nat`:
    --   inclusive (<=): hi - lo + 1
    --   exclusive (<):  hi - lo
    let tripInt ← if exclusive then
      Meta.mkAppM ``HSub.hSub #[limitLean, counterInit]
    else
      Meta.mkAppM ``HAdd.hAdd
        #[← Meta.mkAppM ``HSub.hSub #[limitLean, counterInit], toExpr (1 : Int)]
    let tripNat ← Meta.mkAppM ``Int.toNat #[tripInt]
    -- Collect the accumulator variables: variables assigned in bodyNoStep, except the counter.
    let allModified := (Imperative.Block.modifiedVars bodyNoStep).map (·.name) |>.eraseDups
    let accVars := allModified.filter (· != counterName)
    -- Get initial values and types.
    let accInits ← accVars.mapM fun v =>
      match store[v]? with
      | some e => return e
      | none => throwError s!"extract_def: loop accumulator '{v}' not found in store"
    let accTypes ← accInits.mapM Meta.inferType
    -- Build a `List.foldl` for a single accumulator.  For multiple accumulators
    -- we would need to build a tuple, which is not yet supported.
    match accVars, accInits, accTypes with
    | [accName], [accInit], [accType] =>
      let listRange ← Meta.mkAppM ``List.range #[tripNat]
      let foldLambda ←
        Meta.withLocalDecl `acc .default accType fun accFv =>
        Meta.withLocalDecl `j .default (.const ``Nat []) fun jNat => do
          let jInt ← Meta.mkAppM ``Int.ofNat #[jNat]
          let iVal ← Meta.mkAppM ``HAdd.hAdd #[counterInit, jInt]
          let mut loopStore := store
          loopStore := loopStore.insert counterName iVal
          loopStore := loopStore.insert accName accFv
          let finalStore ← executeStmts ctx loopStore bodyNoStep
          let some newAcc := finalStore[accName]?
            | throwError s!"extract_def: accumulator '{accName}' not assigned in loop body"
          Meta.mkLambdaFVars #[accFv, jNat] newAcc
      let result ← Meta.mkAppM ``List.foldl #[foldLambda, accInit, listRange]
      let mut finalStore := store
      finalStore := finalStore.insert accName result
      let finalI ← Meta.mkAppM ``HAdd.hAdd
          #[counterInit, ← Meta.mkAppM ``Int.ofNat #[tripNat]]
      finalStore := finalStore.insert counterName finalI
      return finalStore
    | [], _, _ =>
      throwError "extract_def: counting loop with no accumulator variables is not supported"
    | _, _, _ =>
      throwError s!"extract_def: counting loop with multiple accumulator variables \
            ({accVars}) is not yet supported"

/--
Replace `Bool.casesOn motive (decide p inst) falseCase trueCase` with
`@ite ty p inst trueCase falseCase` throughout an expression.
-/
partial def simpBoolCasesOn (e : Lean.Expr) : MetaM Lean.Expr :=
  match e with
  | .app (.app (.app (.app (.const ``Bool.casesOn [u]) motive) cond) falseCase) trueCase => do
    let cond'      ← simpBoolCasesOn cond
    let falseCase' ← simpBoolCasesOn falseCase
    let trueCase'  ← simpBoolCasesOn trueCase
    match cond' with
    | .app (.app (.const ``decide []) prop) decInst => do
      let ty ← Meta.inferType trueCase'
      return mkApp5 (.const ``ite [u]) ty prop decInst trueCase' falseCase'
    | _ =>
      return mkApp4 (.const ``Bool.casesOn [u]) motive cond' falseCase' trueCase'
  | .app f a         => return .app (← simpBoolCasesOn f) (← simpBoolCasesOn a)
  | .lam n t b bi    => return .lam n t (← simpBoolCasesOn b) bi
  | .letE n t v b nd => return .letE n t (← simpBoolCasesOn v) (← simpBoolCasesOn b) nd
  | _                => return e

/-- Core of `translateProcedure`: build the lambda body using `ctx`. -/
private def translateProcedureBody (ctx : ExtractCtx) (proc : Core.Procedure) : MetaM Lean.Expr := do
  let inputsList := proc.header.inputs.toList
  let declSpecs ← inputsList.mapM fun (id, ty) => do
    let leanTy ← translateTy ctx ty
    return (Name.mkSimple id.name, BinderInfo.default, fun _ : Array Lean.Expr => pure leanTy)
  Meta.withLocalDecls declSpecs.toArray fun fvars => do
    let store := (inputsList.zip fvars.toList).foldl
      (fun s ((id, _), fv) => s.insert id.name fv) {}
    let finalStore ← executeStmts ctx store proc.body
    let outputsList := proc.header.outputs.toList
    let outputExprs ← outputsList.mapM fun (id, _) =>
      match finalStore[id.name]? with
      | some e => return e
      | none   => throwError s!"extract_def: output '{id.name}' was not assigned"
    if outputExprs.isEmpty then throwError "extract_def: procedure has no outputs"
    if outputExprs.length > 1 then throwError "extract_def: multiple outputs are not yet supported"
    let resultExpr ← simpBoolCasesOn outputExprs[0]!
    Meta.mkLambdaFVars fvars resultExpr

/--
Build the Lean arrow type and a canonical default value for a procedure's signature.
The default value is a lambda that ignores all inputs and returns `default` for the
output type.  It is used as the opaque stub's body so that the stub compiles without
`sorry`.
-/
private def buildFunTypeAndDefault (ctx : ExtractCtx) (proc : Core.Procedure)
    : MetaM (Lean.Expr × Lean.Expr) := do
  let inputsList  := proc.header.inputs.toList
  let outputsList := proc.header.outputs.toList
  unless outputsList.length == 1 do
    throwError "extract_def: multiple outputs are not yet supported"
  let outputType ← translateTy ctx outputsList[0]!.2
  let inputTypes ← inputsList.mapM fun (_, ty) => translateTy ctx ty
  let funType    ← inputTypes.foldrM (fun a b => liftM (mkArrow a b)) outputType
  -- Build a default value: fun _ ... _ => (default : outputType)
  let u       ← Meta.getLevel outputType
  let inhInst ← Meta.synthInstance (.app (.const ``Inhabited [u]) outputType)
  let dflt    ← Meta.mkAppOptM ``default #[some outputType, some inhInst]
  let dflt    ← instantiateMVars dflt
  let defaultVal := inputTypes.foldr (fun inTy acc => .lam `_ inTy acc .default) dflt
  return (funType, defaultVal)

/--
Build one case argument for `T.rec` from a Boole constructor.

For each constructor field `f : F`:
  - If `F` is the inductive type being recursed over, bind `(f : F)` then `(ih_f : RetType)`.
  - Otherwise, bind only `(f : F)`.

The procedure body is symbolically executed with the structural parameter bound to the
full constructor application, and each recursive field's free variable mapped to its IH.
A final `Meta.whnf` step reduces `casesOn`-over-constructor redexes so the resulting
lambda is definitionally clean.
-/
private def buildStructuralCase (ctx : ExtractCtx) (proc : Core.Procedure)
    (structParamName : String) (leanIndType : Lean.Expr) (indName : Name)
    (typeArgs : Array Lean.Expr)
    (booleConstr : Lambda.LConstr Unit) (leanCtorName : Name)
    (retType : Lean.Expr)
    (extraInputs : List (String × Lean.Expr) := []) : MetaM Lean.Expr := do
  -- Collect (fieldName, leanType, isRecursive) for each constructor field in declaration order.
  let fieldInfo ← booleConstr.args.mapM fun (id, booleTy) => do
    let leanTy ← translateTyWithMap ctx.typeMap booleTy
    let isRec  := leanTy.getAppFn.constName? == some indName
    return (id.name, leanTy, isRec)
  -- Lean 4's recursor convention: ALL constructor fields first (in declaration order),
  -- then IHs for each recursive field (in their declaration order).
  -- e.g. for node (left : T) (value : Int) (right : T):
  --   left, value, right, ih_left, ih_right
  let mut decls : Array (Name × BinderInfo × (Array Lean.Expr → MetaM Lean.Expr)) := #[]
  for (fname, fTy, _) in fieldInfo do
    let fTy' := fTy
    decls := decls.push (Name.mkSimple fname, .default, fun _ => pure fTy')
  for (fname, _, isRec) in fieldInfo do
    if isRec then
      let retType' := retType
      decls := decls.push (Name.mkSimple s!"ih_{fname}", .default, fun _ => pure retType')
  -- Extra (non-structural) inputs follow the IH binders.
  for (ename, eTy) in extraInputs do
    let eTy' := eTy
    decls := decls.push (Name.mkSimple ename, .default, fun _ => pure eTy')
  Meta.withLocalDecls decls fun allFvars => do
    -- First fieldInfo.size fvars are the constructor fields in declaration order.
    -- The remaining fvars are IHs for recursive fields, also in declaration order.
    let mut nameToFvar : Std.HashMap String Lean.Expr := {}
    let mut srr        : Std.HashMap FVarId Lean.Expr := {}
    let mut fieldIdx := 0
    for (fname, _, _) in fieldInfo do
      nameToFvar := nameToFvar.insert fname allFvars[fieldIdx]!
      fieldIdx := fieldIdx + 1
    let mut ihIdx := fieldInfo.length
    let mut recIdx := 0
    for (_, _, isRec) in fieldInfo do
      if isRec then
        let fieldFvar := allFvars[recIdx]!
        let ihFvar    := allFvars[ihIdx]!
        srr := srr.insert fieldFvar.fvarId! ihFvar
        ihIdx := ihIdx + 1
      recIdx := recIdx + 1
    -- Constructor applied to field vars in DECLARATION order.
    let declOrderFvars := (fieldInfo.map fun (fname, _, _) => nameToFvar[fname]!).toArray
    let ctorApp ← Meta.mkAppOptM leanCtorName (typeArgs.map some ++ declOrderFvars.map some)
    -- Execute the body with the structural param bound to the constructor.
    let recCtx := { ctx with
      selfProc         := some (proc.header.name.name, .const ``Unit [])  -- dummy; srr handles it
      structRecResults := srr }
    -- Seed the store: structural param → constructor, extra inputs → their fvars.
    -- ihIdx now points just past the last IH fvar, i.e. at the first extra-input fvar.
    let mut initStore := ({} : Store).insert structParamName ctorApp
    for (ename, _) in extraInputs do
      initStore := initStore.insert ename allFvars[ihIdx]!
      ihIdx := ihIdx + 1
    let finalStore ← executeStmts recCtx initStore proc.body
    let outputName := proc.header.outputs.toList[0]!.1.name
    let some resultExpr := finalStore[outputName]?
      | throwError s!"extract_def (structural): output '{outputName}' not assigned"
    -- Instantiate any metavariables before reduction/abstraction.
    let resultExpr ← instantiateMVars resultExpr
    -- Reduce casesOn-over-ctor redexes so the case body is clean.
    let resultExpr ← Meta.whnf resultExpr
    let resultExpr ← instantiateMVars resultExpr
    Meta.mkLambdaFVars allFvars resultExpr

/--
Try to generate a transparent structurally-recursive Lean expression for a procedure.

Applies when the procedure has exactly one input parameter of a user-defined inductive type.
The result is `T.rec motive case₀ … caseₙ`, which is transparent to Lean's kernel and
allows correctness theorems to be proved by `rfl` or `simp`.

Returns `none` if the procedure does not meet these criteria (e.g., has multiple inductive
parameters), falling back to the `@[implemented_by]` opaque approach.
-/
private def tryStructuralRec (ctx : ExtractCtx) (proc : Core.Procedure)
    : MetaM (Option Lean.Expr) := do
  -- Structural recursion requires at least one input; the FIRST must be an inductive type.
  let inputs := proc.header.inputs.toList
  let some (paramId, paramBooleTy) := inputs.head? | return none
  let .tcons tyName [] := paramBooleTy | return none
  let some leanIndType := ctx.typeMap[tyName]? | return none
  let some indName := leanIndType.getAppFn.constName? | return none
  let env ← getEnv
  let some constInfo := env.find? indName | return none
  let .inductInfo indInfo := constInfo | return none
  let mDt := ctx.program.decls.findSome? fun d =>
    match d.getTypeDecl? with
    | some (.data block) => block.find? (·.name == tyName)
    | _ => none
  let some dt := mDt | return none
  unless dt.constrs.length == indInfo.ctors.length do return none
  -- Return type.
  let [(_, retBooleTy)] := proc.header.outputs.toList | return none
  let retType ← translateTy ctx retBooleTy
  let numParams := indInfo.numParams
  let typeArgs  := leanIndType.getAppArgs
  -- Extra (non-structural) inputs: all inputs after the structural parameter.
  let extraInputsRaw := inputs.tail
  let extraInputs ← extraInputsRaw.mapM fun (id, booleTy) => do
    let leanTy ← translateTy ctx booleTy
    return (id.name, leanTy)
  -- IH type = motive applied to a recursive field = (extraTypes → retType).
  let fullRetType ← extraInputs.foldrM (fun (_, eTy) acc => mkArrow eTy acc) retType
  let motive    := Lean.Expr.lam `_ leanIndType fullRetType .default
  -- Build one case expression per constructor.
  let mut caseExprs : Array Lean.Expr := #[]
  for (booleConstr, leanCtorName) in dt.constrs.zip indInfo.ctors do
    let caseExpr ← buildStructuralCase ctx proc paramId.name leanIndType indName
        typeArgs booleConstr leanCtorName fullRetType extraInputs
    caseExprs := caseExprs.push caseExpr
  -- Apply T.rec to the motive and all cases; let Lean infer universe levels.
  let nones := (List.replicate numParams (none : Option Lean.Expr)).toArray
  let recExpr ← Meta.mkAppOptM (Name.str indName "rec")
      (nones ++ #[some motive] ++ caseExprs.map some)
  -- Build the function type (for registering aux constants).
  let inputsList  := proc.header.inputs.toList
  let outputsList := proc.header.outputs.toList
  let outputType  ← translateTy ctx outputsList[0]!.2
  let inputTypes  ← inputsList.mapM fun (_, ty) => translateTy ctx ty
  let funType     ← inputTypes.foldrM (fun a b => liftM (mkArrow a b)) outputType
  --
  -- Two-phase registration for computability + provability:
  --
  -- recTranspName: added kernel-only (addDecl, not addAndCompile) with the T.rec body.
  --   → Lean's kernel sees the transparent T.rec body; proofs can unfold it.
  -- recImplName:   compiled unsafe impl using casesOn + self-ref via recTranspName.
  --   → The code generator uses this for runtime execution.
  -- @[implemented_by] recTranspName → recImplName ensures #eval uses the computable path.
  --
  let procName    := proc.header.name.name
  let recTranspName ← Lean.mkAuxDeclName (Name.mkSimple s!"_extract_{procName}_spec")
  let recImplName   ← Lean.mkAuxDeclName (Name.mkSimple s!"_extract_{procName}_impl")
  -- Phase 1: add the transparent spec constant (kernel only, no code generation).
  Lean.addDecl (.defnDecl {
    name := recTranspName, levelParams := [], type := funType,
    value := recExpr, hints := .abbrev, safety := .safe, all := [recTranspName]
  })
  -- Phase 2: pre-register the @[implemented_by] redirect before the impl exists.
  Lean.setImplementedBy recTranspName recImplName
  -- Phase 3: build the casesOn-based computable body; self-calls use recTranspName.
  let recRef   := Lean.mkConst recTranspName
  let recCtx   := { ctx with selfProc := some (procName, recRef) }
  let implBody ← translateProcedureBody recCtx proc
  let implBody ← instantiateMVars implBody
  -- Phase 4: compile the unsafe implementation.
  addAndCompile (.defnDecl {
    name := recImplName, levelParams := [], type := funType, value := implBody,
    hints := .abbrev, safety := .unsafe
  })
  return some (Lean.mkConst recTranspName)

/--
Translate a Core procedure to a Lean function expression.

For non-recursive procedures, symbolically executes the body and wraps in lambdas.
For self-recursive procedures over a single user-defined inductive parameter, tries to
generate a transparent `T.rec`-based definition that allows kernel-level proofs.
Otherwise, falls back to a two-phase approach:
  1. Register an opaque (sorry-valued) constant so the name is visible to the kernel.
  2. Add a separate unsafe implementation whose body may reference the opaque.
  3. Register the opaque as `@[implemented_by]` the unsafe implementation.
This mirrors how Lean's own `partial def` elaborator works.
-/
def translateProcedure (ctx : ExtractCtx) (proc : Core.Procedure) : MetaM Lean.Expr := do
  let procName := proc.header.name.name
  if hasSelfCall procName proc.body then
    -- Try to generate a transparent structurally-recursive definition first.
    if let some recExpr ← tryStructuralRec ctx proc then
      return recExpr
    -- Derive two unique names: the public opaque and its unsafe implementation.
    let recName     ← Lean.mkAuxDeclName (Name.mkSimple s!"_extract_{procName}")
    let recImplName ← Lean.mkAuxDeclName (Name.mkSimple s!"_extract_{procName}_impl")
    let (funType, defaultVal) ← buildFunTypeAndDefault ctx proc
    -- Phase 1: add recName as a non-sorry opaque to the kernel so safe code can
    -- reference it.  We use addDecl (not addAndCompile) to avoid baking a stale
    -- default-body LCNF that would compete with the @[implemented_by] redirect.
    Lean.addDecl (.opaqueDecl {
      name := recName, levelParams := [], type := funType,
      value := defaultVal, isUnsafe := false, all := [recName]
    })
    -- Phase 2: register the redirect BEFORE compiling the impl so the impl's LCNF
    -- sees the redirect and emits a self-recursive call to recImplName.
    -- (setParam does not validate that recImplName exists yet, so this is safe.)
    Lean.setImplementedBy recName recImplName
    -- Phase 3: build the body; self-calls use recName (the opaque is in the env now).
    let recRef  := Lean.mkConst recName
    let recCtx  := { ctx with selfProc := some (procName, recRef) }
    let body    ← translateProcedureBody recCtx proc
    let body    ← instantiateMVars body
    -- Phase 4: compile the unsafe implementation; its self-calls (via recName) are
    -- redirected to recImplName by the @[implemented_by] attribute set in Phase 2.
    addAndCompile (.defnDecl {
      name := recImplName, levelParams := [], type := funType, value := body,
      hints := .abbrev, safety := .unsafe
    })
    return recRef
  else
    translateProcedureBody ctx proc

end LeanExtract

end Strata

---------------------------------------------------------------------

public section

open Lean Elab Term Meta

namespace Strata

/--
`extract_def p "ProcName"` elaborates to a Lean function whose body matches
the named procedure in the Strata program `p`.

The function takes one argument per input parameter and returns the single
output parameter value. Only `int` and `bool` types are supported in this
initial version.
-/
syntax (name := extractDefTerm) "extract_def" term:max str : term

private unsafe def elabExtractDefUnsafe
    (stx : Lean.Syntax) (expectedType : Option Lean.Expr) : TermElabM Lean.Expr := do
  let some procName := stx[2].isStrLit?
    | throwError "extract_def: expected a string literal as the second argument"

  -- Elaborate the Strata.Program argument
  let programExpr ← elabTerm stx[1] (some (Lean.mkConst ``Strata.Program))

  -- Build Strata.toCoreProgramForExtract programExpr and evaluate it at meta-time.
  -- We deliberately skip loop elimination here: loops are handled semantically by
  -- the extractor (via executeCountingLoop) rather than being replaced with the
  -- verification-only assert/assume/havoc encoding.
  let toCoreProgramApp := .app (.const ``Strata.toCoreProgramForExtract []) programExpr
  let optCoreProgramTy := .app (.const ``Option [0]) (.const ``Core.Program [])
  let some coreProgram ← Meta.evalExpr (Option Core.Program) optCoreProgramTy toCoreProgramApp
    | throwError "extract_def: could not convert program to Core \
        (check the dialect and that the program is well-formed)"

  -- Look up the named procedure
  let some proc := Core.Program.Procedure.find? coreProgram procName
    | throwError s!"extract_def: procedure '{procName}' not found in the Core program"

  -- Build type and op maps, using the user's expected type annotation when available
  let (typeMap, opMap) ← LeanExtract.buildContextMaps coreProgram proc expectedType
  let ctx : LeanExtract.ExtractCtx := { program := coreProgram, typeMap, opMap }
  LeanExtract.translateProcedure ctx proc

@[implemented_by elabExtractDefUnsafe]
meta opaque elabExtractDefImpl
    (stx : Lean.Syntax) (expectedType : Option Lean.Expr) : TermElabM Lean.Expr

@[term_elab extractDefTerm]
meta def elabExtractDef : TermElab := elabExtractDefImpl

end Strata

end -- public section
