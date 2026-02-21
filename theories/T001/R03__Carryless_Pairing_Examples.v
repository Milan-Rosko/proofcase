(* R03__Carryless_Pairing_Examples.v *)

From Coq Require Import Arith List Bool PeanoNat.
Import ListNotations.

From T001 Require Import R01__Carryless_Pairing_Definitions.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Carryless Pairing — Examples                             *)
(*                                                                       *)
(*  This file provides concrete, vm_compute-friendly examples            *)
(*  that witness the effectivity of the carryless pairing device.        *)
(*                                                                       *)
(*  We instantiate Params with a standard Zeckendorf-style realization   *)
(*  (greedy support + Fibonacci rank) matching the behavior in BHK_R.    *)
(*                                                                       *)
(*************************************************************************)

Module Realization.

  (*
    Rank r(x): first index k such that F k > x.
    Bounded scan with fuel S(S x) (primitive recursive).
  *)

  Fixpoint find_r_aux (x k fuel : nat) : nat :=
    match fuel with
    | 0 => k
    | S fuel' =>
        if Nat.ltb x (F k)
        then k
        else find_r_aux x (S k) fuel'
    end.

  Definition r0 (x : nat) : nat := find_r_aux x 0 (S (S x)).

  (*
    Greedy Zeckendorf support, scanning downward.
  *)

  Fixpoint zeck_greedy_down (k rem : nat) (prev_taken : bool)
    : list nat * nat :=
    match k with
    | 0 => ([], rem)
    | S k' =>
        if prev_taken then
          zeck_greedy_down k' rem false
        else
          if Nat.leb (F k) rem then
            let pr := zeck_greedy_down k' (rem - F k) true in
            (k :: fst pr, snd pr)
          else
            zeck_greedy_down k' rem false
    end.

  Definition Z0 (x : nat) : list nat :=
    fst (zeck_greedy_down (r0 x) x false).

  (*
    Concrete parameter pack.
  *)

  Definition P0 : Params :=
    {| Z := Z0; r := r0 |}.

End Realization.

Module Examples.

  Import Realization.

  (*
    Example 1: x = 1, y = 1
  *)

  Example test_pair_1_1_value :
    pair P0 1 1 = 37.
  Proof. vm_compute. reflexivity. Qed.

  Example test_Z_1 :
    Z P0 1 = [2].
  Proof. vm_compute. reflexivity. Qed.

  Example test_r_1 :
    r P0 1 = 3.
  Proof. vm_compute. reflexivity. Qed.

  Example test_B_1 :
    B P0 1 = 6.
  Proof. vm_compute. reflexivity. Qed.

  Example test_even_band_1 :
    even_band P0 1 = [4].
  Proof. vm_compute. reflexivity. Qed.

  Example test_odd_band_1_1 :
    odd_band P0 1 1 = [9].
  Proof. vm_compute. reflexivity. Qed.

  Example test_Z_pair_1_1 :
    Z P0 (pair P0 1 1) = [9; 4].
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_1_1 :
    unpair P0 (pair P0 1 1) = (1, 1).
  Proof. vm_compute. reflexivity. Qed.

  (*
    Example 2: x = 5, y = 3
  *)

  Example test_pair_5_3_value :
    pair P0 5 3 = 4236.
  Proof. vm_compute. reflexivity. Qed.

  Example test_unpair_pair_5_3 :
    unpair P0 (pair P0 5 3) = (5, 3).
  Proof. vm_compute. reflexivity. Qed.

End Examples.