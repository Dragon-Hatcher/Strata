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

namespace LeanExtract

/-- A symbolic store mapping variable names to their current Lean-expression values. -/
abbrev Store := Std.HashMap String Lean.Expr

/-- Context threaded through extraction: the program, a map from user-defined type names
to their Lean type expressions, and an optional self-reference for recursive procedures. -/
structure ExtractCtx where
  program  : Core.Program
  /-- Maps Boole datatype name (e.g. `"List"`) to its Lean type expr (e.g. `List Int`). -/
  typeMap  : Std.HashMap String Lean.Expr := {}
  /-- When extracting a recursive procedure, holds `(procName, selfExpr)` so that
      recursive calls are replaced by applications of the partial def being built. -/
  selfProc : Option (String × Lean.Expr) := none

/-- Check whether a procedure's body contains a self-recursive call. -/
private partial def hasSelfCall (procName : String) (stmts : List Core.Statement) : Bool :=
  stmts.any fun
    | .cmd (.call n _ _)  => n == procName
    | .ite _ t e _        => hasSelfCall procName t || hasSelfCall procName e
    | .block _ body _     => hasSelfCall procName body
    | _                   => false

/-- Detect if a Boole datatype is a singly-linked list of `int` and return the
    corresponding Lean type (`List Int`). -/
private def tryMapListDatatype (dt : Lambda.LDatatype Unit) : Option Lean.Expr :=
  let nilOpt  := dt.constrs.find? (·.args.isEmpty)
  let consOpt := dt.constrs.find? (·.args.length == 2)
  match nilOpt, consOpt with
  | some _, some cons =>
    let (_, headTy) := cons.args[0]!
    let (_, tailTy) := cons.args[1]!
    if headTy == .tcons "int" [] && tailTy == .tcons dt.name [] then
      some (.app (.const ``List [.zero]) (.const ``Int []))
    else none
  | _, _ => none

/-- Build the type map by scanning the program's type declarations. -/
def buildTypeMap (program : Core.Program) : Std.HashMap String Lean.Expr :=
  program.decls.foldl (fun m d =>
    match d.getTypeDecl? with
    | some (.data dtBlock) =>
      dtBlock.foldl (fun m dt =>
        match tryMapListDatatype dt with
        | some ty => m.insert dt.name ty
        | none    => m) m
    | _ => m) {}

/-- Translate a monomorphic Core type to a Lean type expression. -/
def translateTy (ctx : ExtractCtx) : Lambda.LMonoTy → MetaM Lean.Expr
  | .tcons "int" []           => return .const ``Int []
  | .tcons "bool" []          => return .const ``Bool []
  | .tcons "Sequence" [elem]  => do
    let leanElem ← translateTy ctx elem
    Meta.mkAppM ``List #[leanElem]
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
private def applyBinOp (opName : String) (e1 e2 : Lean.Expr) : MetaM Lean.Expr := do
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
  -- User-defined list constructor: Cons(head, tail) → head :: tail
  | "Cons" => Meta.mkAppM ``List.cons #[e1, e2]
  | _ => throwError s!"extract_def: unsupported binary op '{opName}'"

/-- Apply a unary Core operator to a translated Lean expression. -/
private def applyUnaryOp (opName : String) (e : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  | "Int.Neg"         => Meta.mkAppM ``Neg.neg #[e]
  | "Bool.Not"        => return mkApp (.const ``Bool.not []) e
  | "Sequence.length" => do
    let n ← Meta.mkAppM ``List.length #[e]
    Meta.mkAppM ``Int.ofNat #[n]
  -- User-defined list ops — names follow Boole's `TypeName..field!` convention
  | op =>
    if op.endsWith "..isNil" || op == "isNil" then do
      let listTy ← inferType e
      let elemTy := listTy.appArg!
      Meta.mkAppOptM ``List.isEmpty #[some elemTy, some e]
    else if op.endsWith "..isCons" || op == "isCons" then do
      let listTy ← inferType e
      let elemTy := listTy.appArg!
      let isEmpty ← Meta.mkAppOptM ``List.isEmpty #[some elemTy, some e]
      return mkApp (.const ``Bool.not []) isEmpty
    else if op.endsWith "..head!" then
      Meta.mkAppM ``List.head! #[e]
    else if op.endsWith "..tail!" || op.endsWith "..tail" then
      Meta.mkAppM ``List.tail #[e]
    else if op.endsWith "..head" then do
      let listTy ← Meta.inferType e
      let elemTy := listTy.appArg!
      let u    ← Meta.getLevel elemTy
      let inst ← Meta.synthInstance (.app (.const ``Inhabited [u]) elemTy)
      let dflt ← Meta.mkAppOptM ``default #[some elemTy, some inst]
      Meta.mkAppM ``List.headD #[e, dflt]
    else
      throwError s!"extract_def: unsupported unary op '{op}'"

/-- Apply a ternary Core operator to three translated Lean expressions. -/
private def applyTernaryOp (opName : String) (e1 e2 e3 : Lean.Expr) : MetaM Lean.Expr := do
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
  | .const () (.realConst _)
  | .const () (.bitvecConst _ _) =>
    throwError "extract_def: bitvec/real/string constants are not supported"
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
    applyTernaryOp id.name e1' e2' e3'
  -- Binary application: (op e1) e2
  | .app () (.app () (.op () id _) e1) e2 => do
    let e1' ← translateExpr ctx store e1
    let e2' ← translateExpr ctx store e2
    applyBinOp id.name e1' e2'
  -- Unary application: op e
  | .app () (.op () id _) e => do
    let e' ← translateExpr ctx store e
    applyUnaryOp id.name e'
  | .app () _ _ =>
    throwError "extract_def: unsupported application form in expression"
  -- Nullary ops: Sequence.empty and user-defined Nil constructors
  | .op () id opTy =>
    match id.name, opTy with
    | "Sequence.empty", some (.tcons "Sequence" [elemTy]) => do
      let leanElem ← translateTy ctx elemTy
      Meta.mkAppOptM ``List.nil #[some leanElem]
    | "Nil", _ => do
      -- Look up the list element type from typeMap
      let leanElemTy ← match opTy with
        | some (.tcons dtName []) =>
          match ctx.typeMap[dtName]? with
          | some lty => pure lty.appArg!
          | none     => pure (.const ``Int [])
        | _ =>
          -- Fallback: pick the element type of the first list type in the map
          match ctx.typeMap.toList.head? with
          | some (_, lty) => pure lty.appArg!
          | none          => pure (.const ``Int [])
      Meta.mkAppOptM ``List.nil #[some leanElemTy]
    | name, _ => throwError s!"extract_def: bare op '{name}' without application"
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
    -- If this is a recursive self-call, apply the partial-def reference
    if let some (selfName, selfExpr) := ctx.selfProc then
      if procName == selfName then
        let recApp := translatedInputs.foldl Lean.mkApp selfExpr
        unless lhsVars.length == 1 do
          throwError s!"extract_def: recursive call to '{procName}' must have exactly 1 output"
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
      let storeT   ← executeStmts ctx store trueBranch
      let storeF   ← executeStmts ctx store falseBranch
      mergeStores condExpr store storeT storeF
    | .ite .nondet _ _ _ =>
      throwError "extract_def: nondeterministic branch conditions are not supported"
    | .block _ body _ => executeStmts ctx store body
    | .loop _ _ _ _ _ =>
      throwError "extract_def: loops must be eliminated before extraction"
    | .exit _ _ => return store
    | .funcDecl _ _ => return store
    | .typeDecl _ _ => return store

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
Translate a Core procedure to a Lean function expression.

For non-recursive procedures, symbolically executes the body and wraps in lambdas.
For self-recursive procedures, uses a two-phase approach:
  1. Register an opaque (sorry-valued) constant so the name is visible to the kernel.
  2. Add a separate unsafe implementation whose body may reference the opaque.
  3. Register the opaque as `@[implemented_by]` the unsafe implementation.
This mirrors how Lean's own `partial def` elaborator works.
-/
def translateProcedure (ctx : ExtractCtx) (proc : Core.Procedure) : MetaM Lean.Expr := do
  let procName := proc.header.name.name
  if hasSelfCall procName proc.body then
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
    (stx : Lean.Syntax) (_ : Option Lean.Expr) : TermElabM Lean.Expr := do
  let some procName := stx[2].isStrLit?
    | throwError "extract_def: expected a string literal as the second argument"

  -- Elaborate the Strata.Program argument
  let programExpr ← elabTerm stx[1] (some (Lean.mkConst ``Strata.Program))

  -- Build Strata.toCoreProgram programExpr and evaluate it at meta-time
  let toCoreProgramApp := .app (.const ``Strata.toCoreProgram []) programExpr
  let optCoreProgramTy := .app (.const ``Option [0]) (.const ``Core.Program [])
  let some coreProgram ← Meta.evalExpr (Option Core.Program) optCoreProgramTy toCoreProgramApp
    | throwError "extract_def: could not convert program to Core \
        (check the dialect and that the program is well-formed)"

  -- Look up the named procedure
  let some proc := Core.Program.Procedure.find? coreProgram procName
    | throwError s!"extract_def: procedure '{procName}' not found in the Core program"

  -- Symbolically translate the procedure to a Lean term
  let typeMap := LeanExtract.buildTypeMap coreProgram
  let ctx : LeanExtract.ExtractCtx := { program := coreProgram, typeMap }
  LeanExtract.translateProcedure ctx proc

@[implemented_by elabExtractDefUnsafe]
meta opaque elabExtractDefImpl
    (stx : Lean.Syntax) (expectedType : Option Lean.Expr) : TermElabM Lean.Expr

@[term_elab extractDefTerm]
meta def elabExtractDef : TermElab := elabExtractDefImpl

end Strata

end -- public section
