/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-!
OTP (one-time pad) extracted as Lean functions.

Uses the linked-list variant: `Encrypt` and `Decrypt` are recursive procedures
over a user-defined `List` type, which maps to Lean's built-in `List Int`.
-/

private def otp_program : Strata.Program :=
#strata
program Boole;

datatype List () { Nil(), Cons(head: int, tail: List) };

rec function EncryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head(key) + List..head!(message),
    EncryptSpec(List..tail(key), List..tail!(message))
  )
};

rec function DecryptSpec (@[cases] key : List, message : List) : List
{
  if List..isNil(key) then Nil()
  else Cons(
    List..head!(message) - List..head(key),
    DecryptSpec(List..tail(key), List..tail!(message))
  )
};

procedure Encrypt(key : List, message : List) returns (cipher : List)
spec
{
  ensures cipher == EncryptSpec(key, message);
}
{
  if (List..isNil(key)) {
    cipher := Nil();
  } else {
    var t : List;
    call t := Encrypt(List..tail!(key), List..tail!(message));
    cipher := Cons(List..head!(key) + List..head!(message), t);
  }
};

procedure Decrypt(key : List, message : List) returns (result : List)
spec
{
  ensures result == DecryptSpec(key, message);
}
{
  if (List..isNil(key)) {
    result := Nil();
  } else {
    var t : List;
    call t := Decrypt(List..tail!(key), List..tail!(message));
    result := Cons(List..head!(message) - List..head!(key), t);
  }
};

#end

def strata_encrypt : List Int → List Int → List Int :=
  extract_def otp_program "Encrypt"

def strata_decrypt : List Int → List Int → List Int :=
  extract_def otp_program "Decrypt"

/-!
Lean reference implementations for encrypt / decrypt.
-/

def lean_encrypt : List Int → List Int → List Int
  | [], _ => []
  | k :: ks, m :: ms => (k + m) :: lean_encrypt ks ms
  | _ :: _, [] => []

def lean_decrypt : List Int → List Int → List Int
  | [], _ => []
  | k :: ks, c :: cs => (c - k) :: lean_decrypt ks cs
  | _ :: _, [] => []

/-!
Smoke-test: check that encrypt and decrypt round-trip on a concrete example.
`strata_encrypt`/`strata_decrypt` are implemented through an opaque placeholder
(needed to express self-recursion in the kernel); at runtime the actual
implementation runs via `@[implemented_by]`, so `#eval` works normally.
-/
#eval
  let key  : List Int := [1, 2, 3]
  let msg  : List Int := [10, 20, 30]
  let enc  := strata_encrypt key msg
  let dec  := strata_decrypt key enc
  (enc, dec)  -- expected: ([11, 22, 33], [10, 20, 30])

