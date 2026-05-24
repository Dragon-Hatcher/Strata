/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
Demonstrates `extract_def` with `Sequence` inputs and outputs.
The procedure prepends an element to a sequence using only sequence
primitives (`Sequence.empty`, `Sequence.build`, `Sequence.append`).
The extracted Lean function is definitionally equal to `List.cons`.
-/

private def prepend_program : Strata.Program :=
#strata
program Boole;

procedure Prepend(x : int, s : Sequence int) returns (result : Sequence int)
spec {
  ensures Sequence.length(result) == Sequence.length(s) + 1;
}
{
  result := Sequence.append(Sequence.build(Sequence.take(s, 0), x), s);
};
#end

theorem prepend_program_smt_vcs_correct : Strata.smtVCsCorrect prepend_program := by
  gen_smt_vcs
  all_goals (try grind)

def lean_prepend (x : Int) (s : List Int) : List Int := x :: s

def strata_prepend : Int → List Int → List Int :=
  extract_def prepend_program "Prepend"

theorem prepend_correct : ∀ x : Int, ∀ s : List Int,
    strata_prepend x s = lean_prepend x s := by
  intro x s; rfl
