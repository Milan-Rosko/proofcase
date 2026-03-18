(* T001__Extraction_Interface.v *)

From Coq Require Import Arith Bool Extraction List PeanoNat.
Import ListNotations.

From T001 Require Import
  R01__Carryless_Pairing_Definitions
  R02__Carryless_Pairing_Correctness
  R03__Carryless_Pairing_Examples.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / T001 -- OCaml Extraction Interface                       *)
(*                                                                       *)
(*  T001 is a small verified carryless pairing package. This file        *)
(*  exposes a compact executable surface around the distinguished        *)
(*  concrete realization `P0`, together with the arithmetic primitives   *)
(*  needed to inspect the encoding.                                      *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
  (1)
    Concrete parameter pack used by the
    executable examples.
*)

Definition carryless_P0 : Params :=
  R03__Carryless_Pairing_Examples.Realization.P0.

(*
  (2)
  Fibonacci data at index n.
*)

Definition carryless_fib_data (n : nat) : nat * nat :=
  fib_pair n.

(*
  (3)
  Concrete Zeckendorf support
  extractor for the distinguished
  realization.
*)

Definition carryless_support_P0 (n : nat) : list nat :=
  Z carryless_P0 n.

(*
  (4)
  Concrete rank function for the
  distinguished realization.
*)

Definition carryless_rank_P0 (n : nat) : nat :=
  r carryless_P0 n.

(*
  (5)
  Even-band projection specialized to
  `P0`.
*)

Definition carryless_even_band_P0 (x : nat) : list nat :=
  even_band carryless_P0 x.

(*
  (6)
  Odd-band projection specialized to
  `P0`.
*)

Definition carryless_odd_band_P0 (x y : nat) : list nat :=
  odd_band carryless_P0 x y.

(*
  (7)
  Carryless pairing specialized to
  `P0`.
*)

Definition carryless_pair_P0 (x y : nat) : nat :=
  pair carryless_P0 x y.

(*
  (8)
  Zeckendorf support of the encoded
  pair value.
*)

Definition carryless_encoded_support_P0 (x y : nat) : list nat :=
  carryless_support_P0 (carryless_pair_P0 x y).

(*
  (9)
  Carryless unpairing specialized to
  `P0`.
*)

Definition carryless_unpair_P0 (n : nat) : nat * nat :=
  unpair carryless_P0 n.

(*
  (10)
  One-step roundtrip utility for the
  concrete instance.
*)

Definition carryless_roundtrip_P0 (x y : nat) : nat * nat :=
  carryless_unpair_P0 (carryless_pair_P0 x y).

(*
  (11)
  Boolean check that the roundtrip
  returns the original inputs.
*)

Definition carryless_roundtrip_okb_P0 (x y : nat) : bool :=
  match carryless_roundtrip_P0 x y with
  | (x', y') => andb (Nat.eqb x x') (Nat.eqb y y')
  end.

End Extraction_Interface.

Set Extraction Output Directory "T001_Extraction".
Extraction Language OCaml.

Extraction "Carryless_Pairing.ml"
  fib_pair
  fib
  sum_fib
  two
  two_j_minus1
  is_even
  is_odd
  div2
  R03__Carryless_Pairing_Examples.Realization.find_r_aux
  R03__Carryless_Pairing_Examples.Realization.r0
  R03__Carryless_Pairing_Examples.Realization.zeck_greedy_down
  R03__Carryless_Pairing_Examples.Realization.Z0
  carryless_P0
  carryless_fib_data
  carryless_support_P0
  carryless_rank_P0
  even_band
  odd_band
  carryless_even_band_P0
  carryless_odd_band_P0
  pair
  carryless_pair_P0
  carryless_encoded_support_P0
  unpair
  carryless_unpair_P0
  carryless_roundtrip_P0
  carryless_roundtrip_okb_P0.

(*
    ASSUMPTION The abstract correctness
    theorems remain parameterized by
    the Zeckendorf specification
    hypotheses, while the concrete `P0`
    examples are closed vm_compute
    witnesses.
*)

Print Assumptions unpair_pair.
Print Assumptions pair_inj.
Print Assumptions
  R03__Carryless_Pairing_Examples.Examples.test_unpair_pair_5_3.
