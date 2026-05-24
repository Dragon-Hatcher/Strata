/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
Examples of `extract_def` with user-defined algebraic data types.

The expected-type annotation drives the Boole→Lean type mapping: for each input
or output that has a user-defined Boole datatype, `extract_def` finds the matching
Lean inductive in the environment and uses its `casesOn` eliminator to build
constructors, testers, and field destructors generically.  No type-specific logic
is hard-coded.

Three examples, each mapping a different Boole datatype to a Lean type:

1. `Maybe  → Option Int`  (standard Lean `Option`)
2. `Result → ExResult`    (user-defined Lean inductive, two 1-arg constructors)
3. `Tree   → ExTree`      (user-defined recursive inductive, procedure with two
                           simultaneous recursive calls)
-/

-- ---------------------------------------------------------------------------
-- Example 1: Maybe → Option Int
-- ---------------------------------------------------------------------------

/-!
Boole `Maybe` with constructors `Nothing()` and `Just(val : int)`.
`PositiveOnly` wraps a positive integer in `Just`, returning `Nothing` otherwise.
The expected type `Int → Option Int` tells `extract_def` that `Maybe` maps to
`Option Int`; testers and destructors are built from `Option.casesOn`.
-/

private def maybe_program : Strata.Program :=
#strata
program Boole;

datatype Maybe () { Nothing(), Just(val: int) };

procedure PositiveOnly(x : int) returns (result : Maybe)
spec {
  ensures 0 == 0;
}
{
  if (x > 0) {
    result := Just(x);
  } else {
    result := Nothing();
  }
};
#end

def strata_positive_only : Int → Option Int :=
  extract_def maybe_program "PositiveOnly"

def lean_positive_only (x : Int) : Option Int :=
  if x > 0 then some x else none

#eval (strata_positive_only 5, strata_positive_only 0, strata_positive_only (-3))
-- (some 5, none, none)

theorem positive_only_correct : ∀ x : Int,
    strata_positive_only x = lean_positive_only x := by
  intro x; simp only [strata_positive_only, lean_positive_only]

-- ---------------------------------------------------------------------------
-- Example 2: Result → ExResult
-- ---------------------------------------------------------------------------

/-!
A user-defined `ExResult` with constructors `ok` and `err`.
`GetOrElse` returns the wrapped value on `Ok`, or a fallback integer on `Err`.
The expected type `ExResult → Int → Int` drives the mapping of Boole's `Result`
datatype to `ExResult`.
-/

inductive ExResult : Type where
  | ok  (val  : Int) : ExResult
  | err (code : Int) : ExResult
  deriving Repr, Inhabited

private def result_program : Strata.Program :=
#strata
program Boole;

datatype Result () { Ok(val: int), Err(code: int) };

procedure GetOrElse(r : Result, fallback : int) returns (result : int)
spec {
  ensures 0 == 0;
}
{
  if (Result..isOk(r)) {
    result := Result..val!(r);
  } else {
    result := fallback;
  }
};
#end

def strata_get_or_else : ExResult → Int → Int :=
  extract_def result_program "GetOrElse"

def lean_get_or_else : ExResult → Int → Int
  | .ok v,  _ => v
  | .err _, d => d

#eval
  let ok  : ExResult := .ok 42
  let err : ExResult := .err 7
  (strata_get_or_else ok 0, strata_get_or_else err 0)
-- (42, 0)

theorem get_or_else_correct : ∀ r : ExResult, ∀ d : Int,
    strata_get_or_else r d = lean_get_or_else r d := by
  intro r d
  match r with
  | .ok v  => simp only [strata_get_or_else, lean_get_or_else]
  | .err _ => simp only [strata_get_or_else, lean_get_or_else]

-- ---------------------------------------------------------------------------
-- Example 3: Tree → ExTree  (two simultaneous recursive calls)
-- ---------------------------------------------------------------------------

/-!
A user-defined `ExTree` with a nullary `leaf` constructor and a 3-field `node`.
`SumTree` sums all node values via two simultaneous recursive calls; this
exercises the two-phase `@[implemented_by]` approach for self-recursive
procedures, now applied to a type with three-argument constructors.
-/

inductive ExTree : Type where
  | leaf : ExTree
  | node (left : ExTree) (value : Int) (right : ExTree) : ExTree
  deriving Repr, Inhabited

private def tree_program : Strata.Program :=
#strata
program Boole;

datatype Tree () { Leaf(), Node(left: Tree, value: int, right: Tree) };

procedure SumTree(t : Tree) returns (result : int)
spec {
  ensures 0 == 0;
}
{
  if (Tree..isLeaf(t)) {
    result := 0;
  } else {
    var l : int;
    var r : int;
    call l := SumTree(Tree..left!(t));
    call r := SumTree(Tree..right!(t));
    result := Tree..value!(t) + l + r;
  }
};
#end

def strata_sum_tree : ExTree → Int :=
  extract_def tree_program "SumTree"

def lean_sum_tree : ExTree → Int
  | .leaf       => 0
  | .node l v r => lean_sum_tree l + v + lean_sum_tree r

#eval
  let t : ExTree := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)
  (strata_sum_tree t, lean_sum_tree t)  -- (6, 6)

theorem sum_tree_correct : ∀ t : ExTree,
    strata_sum_tree t = lean_sum_tree t := by
  intro t; induction t with
  | leaf => rfl
  | node l v r ihl ihr =>
      simp only [lean_sum_tree, ← ihl, ← ihr]
      -- The extracted body computes `v + l + r`; lean_sum_tree uses `l + v + r`.
      -- Establish the kernel reduction, then let omega handle the commutativity.
      have h : strata_sum_tree (.node l v r) = v + strata_sum_tree l + strata_sum_tree r := rfl
      omega

