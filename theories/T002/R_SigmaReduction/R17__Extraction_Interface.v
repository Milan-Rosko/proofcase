(* R17__Extraction_Interface.v *)

From Coq Require Import Extraction.

From T002 Require Import
  R00__Degree_Framework
  R13__Kernel_API
  R01__Foundation_Fibonacci.

Extraction Language OCaml.
Set Extraction Output Directory "T002extraction".

(*************************************************************************)
(*                                                                       *)
(* Leaf extraction target: checker/compiler-facing computational kernel  *)
(*                                                                       *)
(*************************************************************************)

Extraction "cubic_checker.ml"
  cubic_accepts.

(*************************************************************************)
(*                                                                       *)
(* Leaf extraction target: cubic compiler API                            *)
(*                                                                       *)
(*************************************************************************)

Extraction "cubic_compiler.ml"
  emit_cubic_system
  emit_single_cubic
  degree.

(*************************************************************************)
(*                                                                       *)
(* Leaf extraction target: carryless pairing utilities                   *)
(*                                                                       *)
(*************************************************************************)

Extraction "carryless_pairing.ml"
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