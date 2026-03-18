(* T001__Comprehension.v *)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T001 Require Import
  R01__Carryless_Pairing_Definitions
  R02__Carryless_Pairing_Correctness
  R03__Carryless_Pairing_Examples.

(*************************************************************************)
(*                                   .                                   *)
(*                                  ___                                  *)
(*                       `  .    .'     `.     .  ´                      *)
(*                              /         \                              *)
(*                             |           |                             *)
(*                     _  .    |           |    .  _                     *)
(*                              .  :~~~:  .                              *)
(*                               `. \ / .'                               *)
(*                           .     |_|_|     .                           *)
(*                          ´      (===)      `                          *)
(*                                  `-´                                  *)
(*                                                                       *)
(*    Proofcase / T001 -- Comprehension Layer                            *)
(*                                                                       *)
(*    This file serves as a proof-semantic synopsis and comprehension    *)
(*    aid for project T004. It introduces no new constructive content    *)
(*    or  derivations; but consolidates the core semantics (theorems,    *)
(*    lemmas,  and corollaries, together with their endpoints) into a    *)
(*    unified structure for readability and auditability.                *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  Overview
  --------

  `T001` has one central route and one concrete realization layer.

  (i) COMPUTATIONAL DEFINITION LAYER

      `R01` defines the Fibonacci-based carryless pairing device in plain
      `nat`/`list` terms: even-band and odd-band encodings, their reassembly by
      `pair`, and the structural inverse candidate `unpair`.

  (ii) ABSTRACT CORRECTNESS LAYER

      `R02` proves the main theorem `unpair (pair x y) = (x, y)` under an
      explicit Zeckendorf-style specification for the abstract parameter pack
      `P`. This isolates the pairing argument from the existence/uniqueness
      theory of concrete Zeckendorf realizations.

  (iii) CONCRETE REALIZATION LAYER

      `R03` instantiates the abstract device with a greedy support extractor
      `Z0`, a bounded rank search `r0`, and a concrete parameter pack `P0`,
      then records several `vm_compute` examples.
*)

(*************************************************************************)
(*                                                                       *)
(*                     COMPUTATIONAL DEFINITION LAYER                    *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  FIBONACCI AND BASIC ARITHMETIC
*)

Definition audit_fib_pair : nat -> nat * nat :=
  fib_pair.

Definition audit_fib : nat -> nat :=
  fib.

Definition audit_sum_fib : list nat -> nat :=
  sum_fib.

Definition audit_two : nat -> nat :=
  two.

Definition audit_two_j_minus1 : nat -> nat :=
  two_j_minus1.

Definition audit_is_even : nat -> bool :=
  is_even.

Definition audit_is_odd : nat -> bool :=
  is_odd.

Definition audit_div2 : nat -> nat :=
  div2.

(*
  (ii)
  CARRYLESS DEVICE PARAMETERS AND MAPS
*)

Definition audit_Params : Type :=
  Params.

Definition audit_B : audit_Params -> nat -> nat :=
  B.

Definition audit_even_band :
  audit_Params -> nat -> list nat :=
  even_band.

Definition audit_odd_band :
  audit_Params -> nat -> nat -> list nat :=
  odd_band.

Definition audit_pair :
  audit_Params -> nat -> nat -> nat :=
  pair.

Definition audit_half_even_indices : list nat -> list nat :=
  half_even_indices.

Definition audit_odd_ge_B1 : nat -> nat -> bool :=
  odd_ge_B1.

Definition audit_decode_odd_index : nat -> nat -> nat :=
  decode_odd_index.

Definition audit_y_indices : nat -> list nat -> list nat :=
  y_indices.

Definition audit_unpair :
  audit_Params -> nat -> nat * nat :=
  unpair.

(*************************************************************************)
(*                                                                       *)
(*                      ABSTRACT CORRECTNESS LAYER                       *)
(*                                                                       *)
(*************************************************************************)

(*
  The theorems imported from `R02` are section-parametric in a parameter pack
  `P` together with a Zeckendorf specification. We keep those parameters
  explicit in the audit layer by aliasing the generalized theorems directly.
*)

Definition audit_two_S :=
  two_S.

Definition audit_div2_two :=
  div2_two.

Definition audit_add_sub_cancel_l :=
  add_sub_cancel_l.

Definition audit_map_div2_even_band :=
  @map_div2_even_band.

Definition audit_decode_encode_odd :=
  decode_encode_odd.

Definition audit_map_decode_odd_band :=
  @map_decode_odd_band.

Definition audit_sum_fib_half_even_pair :=
  @sum_fib_half_even_pair.

Definition audit_sum_fib_y_indices_pair :=
  @sum_fib_y_indices_pair.

(*
  Main correctness theorem: under the Zeckendorf specification hypotheses,
  carryless unpairing is a left inverse to carryless pairing.
*)

Definition audit_unpair_pair :=
  @unpair_pair.

(*
  Consequence: the carryless pairing map is injective under the same
  specification.
*)

Definition audit_pair_inj :=
  @pair_inj.

(*************************************************************************)
(*                                                                       *)
(*                    CONCRETE REALIZATION AND EXAMPLES                  *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  Concrete rank/support realization used for executable examples.
*)

Definition audit_find_r_aux :=
  R03__Carryless_Pairing_Examples.Realization.find_r_aux.

Definition audit_r0 :=
  R03__Carryless_Pairing_Examples.Realization.r0.

Definition audit_zeck_greedy_down :=
  R03__Carryless_Pairing_Examples.Realization.zeck_greedy_down.

Definition audit_Z0 :=
  R03__Carryless_Pairing_Examples.Realization.Z0.

Definition audit_P0 :=
  R03__Carryless_Pairing_Examples.Realization.P0.

(*
  (ii)
  vm_compute witnesses showing the concrete device in action.
*)

Definition audit_test_pair_1_1_value :
  pair audit_P0 1 1 = 37 :=
  R03__Carryless_Pairing_Examples.Examples.test_pair_1_1_value.

Definition audit_test_Z_1 :
  Z audit_P0 1 = [2] :=
  R03__Carryless_Pairing_Examples.Examples.test_Z_1.

Definition audit_test_r_1 :
  r audit_P0 1 = 3 :=
  R03__Carryless_Pairing_Examples.Examples.test_r_1.

Definition audit_test_B_1 :
  B audit_P0 1 = 6 :=
  R03__Carryless_Pairing_Examples.Examples.test_B_1.

Definition audit_test_even_band_1 :
  even_band audit_P0 1 = [4] :=
  R03__Carryless_Pairing_Examples.Examples.test_even_band_1.

Definition audit_test_odd_band_1_1 :
  odd_band audit_P0 1 1 = [9] :=
  R03__Carryless_Pairing_Examples.Examples.test_odd_band_1_1.

Definition audit_test_Z_pair_1_1 :
  Z audit_P0 (pair audit_P0 1 1) = [9; 4] :=
  R03__Carryless_Pairing_Examples.Examples.test_Z_pair_1_1.

Definition audit_test_unpair_pair_1_1 :
  unpair audit_P0 (pair audit_P0 1 1) = (1, 1) :=
  R03__Carryless_Pairing_Examples.Examples.test_unpair_pair_1_1.

Definition audit_test_pair_5_3_value :
  pair audit_P0 5 3 = 4236 :=
  R03__Carryless_Pairing_Examples.Examples.test_pair_5_3_value.

Definition audit_test_unpair_pair_5_3 :
  unpair audit_P0 (pair audit_P0 5 3) = (5, 3) :=
  R03__Carryless_Pairing_Examples.Examples.test_unpair_pair_5_3.

(*
  Canonical concrete endpoint alias for audit-facing reading.
*)

Definition audit_concrete_endpoint :
  unpair audit_P0 (pair audit_P0 5 3) = (5, 3) :=
  R03__Carryless_Pairing_Examples.Examples.test_unpair_pair_5_3.

(*************************************************************************)
(*                                                                       *)
(*                                  QED                                  *)
(*                                                                       *)
(*                           Carryless Pairing                           *)
(*                                                                       *)
(*                             PROOF IN STEPS                            *)
(*                                                                       *)
(*    Step 1. Encode `x` into the even band and `y` into the odd band,   *)
(*            then sum the corresponding Fibonacci weights to form       *)
(*            `pair P x y`.                                              *)
(*                                                                       *)
(*    Step 2. Recover the even-band support by filtering the             *)
(*            Zeckendorf support of the paired value on even indices,    *)
(*            and halve those indices to reconstruct `x`.                *)
(*                                                                       *)
(*    Step 3. Recover the odd-band support by filtering on odd indices   *)
(*            above the offset `B P x`, then decode those indices to     *)
(*            reconstruct `y`.                                           *)
(*                                                                       *)
(*    Step 4. Conclude `unpair P (pair P x y) = (x, y)`, and hence       *)
(*            injectivity of `pair P`.                                   *)
(*                                                                       *)
(*                             MECHANIZATION                             *)
(*                                                                       *)
(*              forall x y, unpair P (pair P x y) = (x, y)               *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Under  the  explicit Zeckendorf specification carried in `R02`,    *)
(*    the  carryless  pairing  device  is  correct: decoding a paired    *)
(*    value  returns  exactly  the  original  pair,  and equal paired    *)
(*    values must have equal components.                                 *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    The  theorem  is abstract in the parameter pack `P`; `R03` then    *)
(*    supplies  one  concrete  realization  `audit_P0`  together with    *)
(*    executable examples.                                               *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.

Print Assumptions unpair_pair.
Print Assumptions pair_inj.
