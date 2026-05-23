/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Lean.Meta
import Lean.Elab.Term

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

/-- Translate a monomorphic Core type to a Lean type expression. -/
def translateTy : Lambda.LMonoTy → MetaM Lean.Expr
  | .tcons "int" []  => return .const ``Int []
  | .tcons "bool" [] => return .const ``Bool []
  | ty => throwError s!"extract_def: unsupported type {repr ty}"

/--
Build a `Bool`-branched if-then-else Lean expression.
Emits `Bool.casesOn cond falseCase trueCase`.
-/
def boolIteM (cond trueCase falseCase : Lean.Expr) : MetaM Lean.Expr := do
  let ty    ← Meta.inferType trueCase
  let level ← Meta.getLevel ty
  -- motive: fun (_ : Bool) => ty  (non-dependent return type)
  let motive := Lean.Expr.lam `b (.const ``Bool []) ty .default
  return mkApp4 (.const ``Bool.casesOn [level]) motive cond falseCase trueCase

/-- Wrap a Prop-valued expression in `decide` to get a `Bool`. -/
private def decideExpr (prop : Lean.Expr) : MetaM Lean.Expr := do
  let decInst ← Meta.synthInstance (.app (.const ``Decidable []) prop)
  return mkApp2 (.const ``decide []) prop decInst

/-- Apply a binary Core operator to two translated Lean expressions. -/
private def applyBinOp (opName : String) (e1 e2 : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  -- Integer arithmetic
  | "Int.Add" => Meta.mkAppM ``HAdd.hAdd #[e1, e2]
  | "Int.Sub" => Meta.mkAppM ``HSub.hSub #[e1, e2]
  | "Int.Mul" => Meta.mkAppM ``HMul.hMul #[e1, e2]
  | "Int.Div" | "Int.DivT"   => Meta.mkAppM ``HDiv.hDiv #[e1, e2]
  | "Int.Mod" | "Int.ModT"   => Meta.mkAppM ``HMod.hMod #[e1, e2]
  -- Integer comparisons → Bool via decide
  | "Int.Lt" => decideExpr (← Meta.mkAppM ``LT.lt #[e1, e2])
  | "Int.Le" => decideExpr (← Meta.mkAppM ``LE.le #[e1, e2])
  | "Int.Gt" => decideExpr (← Meta.mkAppM ``GT.gt #[e1, e2])
  | "Int.Ge" => decideExpr (← Meta.mkAppM ``GE.ge #[e1, e2])
  -- Boolean binary ops
  | "Bool.And"     => return mkApp2 (.const ``Bool.and []) e1 e2
  | "Bool.Or"      => return mkApp2 (.const ``Bool.or []) e1 e2
  | "Bool.Implies" => return mkApp2 (.const ``Bool.or [])
                               (mkApp (.const ``Bool.not []) e1) e2
  | "Bool.Equiv"   => decideExpr (← Meta.mkAppM ``Eq #[e1, e2])
  | _ => throwError s!"extract_def: unsupported binary op '{opName}'"

/-- Apply a unary Core operator to a translated Lean expression. -/
private def applyUnaryOp (opName : String) (e : Lean.Expr) : MetaM Lean.Expr := do
  match opName with
  | "Int.Neg"  => Meta.mkAppM ``Neg.neg #[e]
  | "Bool.Not" => return mkApp (.const ``Bool.not []) e
  | _ => throwError s!"extract_def: unsupported unary op '{opName}'"

/-- Translate a Core expression to a Lean expression given a symbolic store. -/
partial def translateExpr (store : Store) : Core.Expression.Expr → MetaM Lean.Expr
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
    let c' ← translateExpr store c
    let t' ← translateExpr store t
    let e' ← translateExpr store e
    boolIteM c' t' e'
  | .eq () e1 e2 => do
    let e1' ← translateExpr store e1
    let e2' ← translateExpr store e2
    decideExpr (← Meta.mkAppM ``Eq #[e1', e2'])
  -- Binary application: (op e1) e2
  | .app () (.app () (.op () id _) e1) e2 => do
    let e1' ← translateExpr store e1
    let e2' ← translateExpr store e2
    applyBinOp id.name e1' e2'
  -- Unary application: op e
  | .app () (.op () id _) e => do
    let e' ← translateExpr store e
    applyUnaryOp id.name e'
  | .app () _ _ =>
    throwError "extract_def: unsupported application form in expression"
  | .op () id _ =>
    throwError s!"extract_def: bare op '{id.name}' without application"
  | .bvar () i =>
    throwError s!"extract_def: unexpected bound variable at index {i}"
  | .abs () _ _ _ =>
    throwError "extract_def: lambda abstractions in procedure bodies are not supported"
  | .quant () _ _ _ _ _ =>
    throwError "extract_def: quantifiers in procedure bodies are not supported"

/-- Merge two branch stores after an if/else, producing conditional values for differing keys. -/
private def mergeStores (cond : Lean.Expr) (baseStore storeT storeF : Store) : MetaM Store := do
  let allKeys := (storeT.toList ++ storeF.toList).map Prod.fst
  let mut merged := baseStore
  let placeholder := Lean.Expr.const ``True []  -- used as a dummy when a key is missing
  for key in allKeys do
    let tVal := storeT[key]? |>.getD (baseStore[key]? |>.getD placeholder)
    let fVal := storeF[key]? |>.getD (baseStore[key]? |>.getD placeholder)
    if tVal == fVal then
      merged := merged.insert key tVal
    else
      merged := merged.insert key (← boolIteM cond tVal fVal)
  return merged

/-- Symbolically execute a list of Core statements, threading the store through. -/
partial def executeStmts (store : Store) (stmts : List Core.Statement) : MetaM Store :=
  stmts.foldlM executeStmt store
where
  /-- Symbolically execute one Core statement. -/
  executeStmt (store : Store) (stmt : Core.Statement) : MetaM Store := do
    match stmt with
    -- Deterministic assignment
    | .cmd (.cmd (.set id (.det e) _)) => do
      return store.insert id.name (← translateExpr store e)
    | .cmd (.cmd (.init id _ (.det e) _)) => do
      return store.insert id.name (← translateExpr store e)
    -- Nondeterministic assignment: placeholder (must be overwritten later)
    | .cmd (.cmd (.set id .nondet _)) => do
      let mv ← Meta.mkFreshExprMVar (Lean.mkConst ``Int)
      return store.insert id.name mv
    | .cmd (.cmd (.init id ty .nondet _)) => do
      let .forAll _ mty := ty
      let leanTy ← try translateTy mty catch _ => pure (Lean.mkConst ``Int)
      let mv ← Meta.mkFreshExprMVar leanTy
      return store.insert id.name mv
    -- Spec annotations: skip
    | .cmd (.cmd (.assert _ _ _))
    | .cmd (.cmd (.assume _ _ _))
    | .cmd (.cmd (.cover  _ _ _)) => return store
    -- Procedure calls: not supported in MVP
    | .cmd (.call procName _ _) =>
      throwError s!"extract_def: procedure calls ('{procName}') are not supported"
    -- If/else
    | .ite (.det condE) trueBranch falseBranch _ => do
      let condExpr ← translateExpr store condE
      let storeT   ← executeStmts store trueBranch
      let storeF   ← executeStmts store falseBranch
      mergeStores condExpr store storeT storeF
    | .ite .nondet _ _ _ =>
      throwError "extract_def: nondeterministic branch conditions are not supported"
    -- Blocks: execute body sequentially
    | .block _ body _ => executeStmts store body
    -- Loops must have been removed by loopElim
    | .loop _ _ _ _ _ =>
      throwError "extract_def: loops must be eliminated before extraction"
    -- Exit: return store unchanged
    | .exit _ _ => return store
    -- Inline function / type declarations: skip
    | .funcDecl _ _ => return store
    | .typeDecl _ _ => return store

/--
Translate a Core procedure to a Lean function expression.

Creates a Lean FVar per input, symbolically executes the body, reads the
output variable(s) from the resulting store, and wraps in lambdas.
-/
def translateProcedure (proc : Core.Procedure) : MetaM Lean.Expr := do
  let inputsList := proc.header.inputs.toList
  let declSpecs ← inputsList.mapM fun (id, ty) => do
    let leanTy ← translateTy ty
    return (Name.mkSimple id.name, BinderInfo.default, fun _ : Array Lean.Expr => pure leanTy)
  Meta.withLocalDecls declSpecs.toArray fun fvars => do
    let store := (inputsList.zip fvars.toList).foldl
      (fun s ((id, _), fv) => s.insert id.name fv) {}
    let finalStore ← executeStmts store proc.body
    let outputsList := proc.header.outputs.toList
    let outputExprs ← outputsList.mapM fun (id, _) =>
      match finalStore[id.name]? with
      | some e => return e
      | none   => throwError s!"extract_def: output '{id.name}' was not assigned"
    if outputExprs.isEmpty then throwError "extract_def: procedure has no outputs"
    if outputExprs.length > 1 then throwError "extract_def: multiple outputs are not yet supported"
    let resultExpr := outputExprs[0]!
    Meta.mkLambdaFVars fvars resultExpr

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
  LeanExtract.translateProcedure proc

@[implemented_by elabExtractDefUnsafe]
meta opaque elabExtractDefImpl
    (stx : Lean.Syntax) (expectedType : Option Lean.Expr) : TermElabM Lean.Expr

@[term_elab extractDefTerm]
meta def elabExtractDef : TermElab := elabExtractDefImpl

end Strata

end -- public section
