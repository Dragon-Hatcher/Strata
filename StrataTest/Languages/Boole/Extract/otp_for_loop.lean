/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
OTP (one-time pad) extracted as Lean functions.

Uses the sequence variant: `Encrypt` and `Decrypt` iterate over a `Sequence int`
using a for loop, mapping to Lean's built-in `List Int`.
-/

private def otp_for_program : Strata.Program :=
#strata
program Boole;

procedure Encrypt(key : Sequence int, message : Sequence int) returns (cipher : Sequence int)
spec
{
  ensures Sequence.length(cipher) == Sequence.length(key);
  ensures (forall i : int :: 0 <= i && i < Sequence.length(key) ==>
    Sequence.select(cipher, i) == Sequence.select(key, i) + Sequence.select(message, i));
}
{
  cipher := Sequence.take(key, 0);
  for i : int := 0 to Sequence.length(key) - 1 by 1
  {
    cipher := Sequence.build(cipher, Sequence.select(key, i) + Sequence.select(message, i));
  }
};

procedure Decrypt(key : Sequence int, cipher : Sequence int) returns (result : Sequence int)
spec
{
  ensures Sequence.length(result) == Sequence.length(key);
  ensures (forall i : int :: 0 <= i && i < Sequence.length(key) ==>
    Sequence.select(result, i) == Sequence.select(cipher, i) - Sequence.select(key, i));
}
{
  result := Sequence.take(key, 0);
  for i : int := 0 to Sequence.length(key) - 1 by 1
  {
    result := Sequence.build(result, Sequence.select(cipher, i) - Sequence.select(key, i));
  }
};

#end

def strata_for_encrypt : List Int → List Int → List Int :=
  extract_def otp_for_program "Encrypt"

def strata_for_decrypt : List Int → List Int → List Int :=
  extract_def otp_for_program "Decrypt"

/-!
Lean reference implementations.
-/

def lean_for_encrypt : List Int → List Int → List Int :=
  List.zipWith (· + ·)

-- Decrypt computes cipher[i] - key[i], so arguments to zipWith are swapped
def lean_for_decrypt (key cipher : List Int) : List Int :=
  List.zipWith (· - ·) cipher key

/-!
Smoke-test: encrypt and decrypt round-trip on a concrete example.
-/
#eval
  let key  : List Int := [1, 2, 3]
  let msg  : List Int := [10, 20, 30]
  let enc  := strata_for_encrypt key msg
  let dec  := strata_for_decrypt key enc
  (enc, dec)  -- expected: ([11, 22, 33], [10, 20, 30])

/-!
Correctness proofs: the extracted functions agree with the Lean reference implementations.

The extracted functions are defined via `List.foldl (List.range n)`, so the proofs go through
two auxiliary lemmas:
1. `foldl_concat_range_eq_map`: relates `foldl`-with-concat over `List.range` to `List.map`.
2. `map_range_getD_eq_zipWith_*`: relates the pointwise map to `List.zipWith`.
-/

private theorem foldl_concat_range_eq_map {α : Type _} (f : Nat → α) (n : Nat) :
    List.foldl (fun acc j => acc.concat (f j)) [] (List.range n) =
    (List.range n).map f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.map_append, ← ih]
    simp [List.concat_eq_append]

private theorem map_range_getD_eq_zipWith_add (key msg : List Int) (h : key.length = msg.length) :
    (List.range key.length).map (fun j => key.getD j 0 + msg.getD j 0) =
    List.zipWith (· + ·) key msg := by
  apply List.ext_getElem
  · simp [h]
  · intro n hn1 hn2
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
    have hk : n < key.length := by simpa using hn1
    have hm : n < msg.length := h ▸ hk
    simp [List.getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hm]

private theorem map_range_getD_eq_zipWith_sub (key cipher : List Int) (h : key.length = cipher.length) :
    (List.range key.length).map (fun j => cipher.getD j 0 - key.getD j 0) =
    List.zipWith (· - ·) cipher key := by
  apply List.ext_getElem
  · simp [List.length_zipWith, h.symm]
  · intro n hn1 hn2
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith]
    have hk : n < key.length := by simpa using hn1
    have hm : n < cipher.length := h ▸ hk
    simp [List.getD, List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hm]

theorem for_encrypt_correct : ∀ key msg : List Int, key.length = msg.length →
    strata_for_encrypt key msg = lean_for_encrypt key msg := by
  intro key msg h
  have hlen : (Int.ofNat key.length - 1 - 0 + 1).toNat = key.length := by
    simp only [Int.ofNat_eq_natCast, Int.sub_zero]; omega
  have hstep : strata_for_encrypt key msg =
      List.foldl (fun acc j => acc.concat (key.getD j 0 + msg.getD j 0)) [] (List.range key.length) := by
    simp only [strata_for_encrypt, hlen]
    congr 1; funext acc j
    simp [Int.ofNat_eq_natCast, Int.toNat_natCast]
  simp only [lean_for_encrypt]
  rw [hstep, foldl_concat_range_eq_map, map_range_getD_eq_zipWith_add key msg h]

theorem for_decrypt_correct : ∀ key cipher : List Int, key.length = cipher.length →
    strata_for_decrypt key cipher = lean_for_decrypt key cipher := by
  intro key cipher h
  have hlen : (Int.ofNat key.length - 1 - 0 + 1).toNat = key.length := by
    simp only [Int.ofNat_eq_natCast, Int.sub_zero]; omega
  have hstep : strata_for_decrypt key cipher =
      List.foldl (fun acc j => acc.concat (cipher.getD j 0 - key.getD j 0)) [] (List.range key.length) := by
    simp only [strata_for_decrypt, hlen]
    congr 1; funext acc j
    simp [Int.ofNat_eq_natCast, Int.toNat_natCast]
  simp only [lean_for_decrypt]
  rw [hstep, foldl_concat_range_eq_map, map_range_getD_eq_zipWith_sub key cipher h]
