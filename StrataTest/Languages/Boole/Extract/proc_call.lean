/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
Demonstrates `extract_def` with inter-procedure calls.
`Quadruple` calls `Double` twice, and the extracted Lean function inlines both.
-/

private def quadruple_program : Strata.Program :=
#strata
program Boole;

procedure Double(x : int) returns (y : int)
spec {
  ensures y == x + x;
}
{
  y := x + x;
};

procedure Quadruple(x : int) returns (result : int)
spec {
  ensures result == x + x + x + x;
}
{
  var d : int;
  call d := Double(x);
  call result := Double(d);
};
#end

theorem quadruple_program_smt_vcs_correct : Strata.smtVCsCorrect quadruple_program := by
  gen_smt_vcs
  all_goals (try grind)

def lean_quadruple (x : Int) : Int := x + x + x + x

def strata_quadruple : Int → Int :=
  extract_def quadruple_program "Quadruple"

theorem quadruple_correct : ∀ x : Int, strata_quadruple x = lean_quadruple x := by
  intro x; simp only [strata_quadruple, lean_quadruple]; omega
