(* RX__Carryless_Pairing_Export.v *)

From Coq Require Import Extraction.

From T001 Require Import R01__Carryless_Pairing_Definitions.
From T001 Require Import R02__Carryless_Pairing_Correctness.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Carryless Pairing — extraction + assumptions             *)
(*                                                                       *)
(*  This file provides two artifacts:                                    *)
(*                                                                       *)
(*    (i)  OCaml extraction of the core carryless pairing definitions.   *)
(*    (ii) An assumptions report for the main correctness results.       *)
(*                                                                       *)
(*************************************************************************)

Extraction Language OCaml.
Set Extraction Output Directory "witness".

Extraction "Carryless_Pairing.ml"
  fib_pair
  F
  sumF
  two
  two_j_minus1
  is_even
  is_odd
  div2
  even_band
  odd_band
  pair
  unpair.

Print Assumptions unpair_pair.
Print Assumptions pair_inj.

