/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

private def find_max_program : Strata.Program :=
#strata
program Boole;

procedure Max(a : int, b : int) returns (max : int)
spec
{
  ensures a <= max && b <= max;
}
{
  if (a > b) {
    max := a;
  } else {
    max := b;
  }
};
#end

theorem find_max_program_smt_vcs_correct : Strata.smtVCsCorrect find_max_program := by
  gen_smt_vcs
  all_goals (try grind)

def lean_max (a b : Int) : Int := if a > b then a else b

def strata_max : Int → Int → Int := extract_def find_max_program "Max"

theorem equivalent : ∀ a b : Int, strata_max a b = lean_max a b := by
  intro a b
  simp only [strata_max, lean_max]
  by_cases h : a > b
  · simp [if_pos h, show decide (a > b) = true from decide_eq_true_iff.mpr h]
  · simp [if_neg h, show decide (a > b) = false from decide_eq_false_iff_not.mpr h]
