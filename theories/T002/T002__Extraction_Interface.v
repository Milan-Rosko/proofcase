(* T002__Extraction_Interface.v *)

From Coq Require Import Arith Bool Extraction List PeanoNat.
Import ListNotations.

From T002 Require Import
  R00__Degree_Framework
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R11__Constraints_Assembly
  R13__Kernel_API
  R21__Pairing_Correctness_P0.

(*************************************************************************)
(*                                                                       *)
(*                                                                       *)
(*                            _                                          *)
(*                        --'  |                                         *)
(*                       (___^ |     .--.                                *)
(*                          )  |   /      \                              *)
(*                         /   |  /        '                             *)
(*                        |    '-'    /     \                            *)
(*                         \         |      |\                           *)
(*                          \    /   \      /\|                          *)
(*                           \  /'____`\   /                             *)
(*                           | ||      \ \ |                             *)
(*                           ( (|       ( (|                             *)
(*                           | ||       | ||                             *)
(*                          / /_(      / /_(                             *)
(*                                                                       *)
(*                                                                       *)
(*    Proofcase / T002 -- OCaml Extraction Interface                     *)
(*                                                                       *)
(*    This  file  specifies  the  extraction  of the development into    *)
(*    OCaml.  It  records  how  executable code is generated from the    *)
(*    definitions  with  computational  content, while proof-specific    *)
(*    material  is erased during extraction. The resulting OCaml code    *)
(*    can then be inspected or executed independently of the original    *)
(*    proofs.                                                            *)
(*                                                                       *)
(*************************************************************************)

(*
  T002 is primarily a proof theoretic semantic package, but its checker,
  compiler, and “carryless” kernel are executable. This file exposes a small
  computational surface for extraction, mirroring the stable API exposed by the
  kernel layer.
*)

Section Extraction_Interface.

(*
  (1)
  Executable checker surface at the public kernel boundary.
*)

Definition checker_accepts (pf : Proof) (target : Form) : bool :=
  cubic_accepts pf target.

(*
  (2)
  Finite polynomial system emitted by the certified compiler.
*)

Definition compiler_system (pf : Proof) (target : Form) : list Polynomial :=
  emit_cubic_system pf target.

(*
  (3)
  Single aggregated cubic equation emitted from the compiled system.
*)

Definition compiler_single_cubic
    (pf : Proof) (target : Form) : Polynomial * Polynomial :=
  emit_single_cubic pf target.

(*
  (4)
  Degree profile of the emitted finite system.
*)

Definition compiler_system_degree_profile
    (pf : Proof) (target : Form) : list nat :=
  map total_degree (compiler_system pf target).

(*
  (5)
  Number of constraints emitted by the compiler.
*)

Definition compiler_system_size
    (pf : Proof) (target : Form) : nat :=
  length (compiler_system pf target).

(*
  (6)
  Degree profile of the aggregated single cubic equation.
*)

Definition compiler_single_cubic_degree_profile
    (pf : Proof) (target : Form) : nat * nat :=
  let eqn := compiler_single_cubic pf target in
  (total_degree (fst eqn), total_degree (snd eqn)).

(*
  (7)
  One bundled executable view of checking plus compilation data.
*)

Definition checker_compiler_summary
    (pf : Proof) (target : Form)
    : bool * nat * list nat * (nat * nat) :=
  ( checker_accepts pf target,
    compiler_system_size pf target,
    compiler_system_degree_profile pf target,
    compiler_single_cubic_degree_profile pf target ).

(*
  (8)
  Carryless pairing specialized to the distinguished `P0` instance.
*)

Definition carryless_pair_P0 (x y : nat) : nat :=
  pair P0 x y.

(*
  (9)
  Carryless unpairing specialized to the distinguished `P0` instance.
*)

Definition carryless_unpair_P0 (n : nat) : nat * nat :=
  unpair P0 n.

(*
  (10)
  One-step roundtrip utility for the `P0` pairing instance.
*)

Definition carryless_roundtrip_P0 (x y : nat) : nat * nat :=
  carryless_unpair_P0 (carryless_pair_P0 x y).

(*
  (11)
  Even-band projection specialized to `P0`.
*)

Definition carryless_even_band_P0 (x : nat) : list nat :=
  even_band P0 x.

(*
  (12)
  Odd-band projection specialized to `P0`.
*)

Definition carryless_odd_band_P0 (x y : nat) : list nat :=
  odd_band P0 x y.

End Extraction_Interface.

Set Extraction Output Directory "T002_Extraction".
Extraction Language OCaml.

Extraction "cubic_checker.ml"
  cubic_accepts
  checker_accepts.

Extraction "cubic_compiler.ml"
  emit_cubic_system
  emit_single_cubic
  degree
  compiler_system_degree_profile
  compiler_system_size
  compiler_single_cubic_degree_profile
  checker_compiler_summary.

Extraction "carryless_pairing.ml"
  fib_pair
  fib
  sum_fib
  two
  two_j_minus1
  is_even
  is_odd
  div2
  even_band
  odd_band
  pair
  unpair
  carryless_pair_P0
  carryless_unpair_P0
  carryless_roundtrip_P0
  carryless_even_band_P0
  carryless_odd_band_P0.

(*************************************************************************)
(*                                                                       *)
(*  KEY ASSUMPTION REPORT                                                *)
(*                                                                       *)
(*  The extraction surface is intended to remain computationally         *)
(*  honest with respect to the certified kernel interface.               *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions cubic_accepts_iff_cubic_witness.
Print Assumptions check_iff_emit_cubic_all_zero.
Print Assumptions emit_single_cubic_degree_le_3.
Print Assumptions unpair_pair_P0.
