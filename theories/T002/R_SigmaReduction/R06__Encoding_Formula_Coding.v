(* R06__Formula_Coding.v *)

From Coq Require Import Arith.
From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax.

Fixpoint enc_form (phi : Form) : nat :=
  match phi with
  | F_Bot => 0
  | F_Imp a b => S (pair P0 (enc_form a) (enc_form b))
  end.