From Coq Require Import ZArith List String Lia Arith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

From T003 Require Import R01__Coeff_types.

(* Auto-generated public variable map for the pinned bounded cubic artifact. *)

Definition ix_u : nat := 18711.
Definition var_u : string := "trace_code".
Lemma ix_u_lt_var_count : (ix_u < var_count)%nat.
Proof.
  apply Nat.ltb_lt.
  vm_compute.
  reflexivity.
Qed.

Definition public_var_indices : list (string * nat) := [("u", ix_u)].
