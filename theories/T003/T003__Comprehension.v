(* T003__Comprehension.v *)

From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

From T003 Require Import
  R00__VarMap
  R01__Coeff_types
  R02__Coefficients
  R03__Degree
  R04__Universal
  R05__Effectivity
  R07__Table_Inspection
  R08__Bounded_Universality.

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
(*    Proofcase / T003 -- Comprehension Layer                            *)
(*                                                                       *)
(*    This file serves as the proof-semantic synopsis for project        *)
(*    T003. It introduces no new constructive content or derivations;    *)
(*    rather, it consolidates the pinned metadata, coefficient-table     *)
(*    semantics, certification gates, and bounded endpoint theorem       *)
(*    into one audit-facing structure.                                   *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  Overview
  --------

  `T003` is a bounded artifact package rather than a uniform reduction family.

  (i) ARTIFACT METADATA AND INPUT PINNING

      The package fixes one concrete coefficient-table cubic artifact together
      with the public variable map placing the external input `u` at the pinned
      coordinate `ix_u`.

  (ii) TABLE CERTIFICATION

      The concrete monomial table `poly` is certified in two orthogonal ways:
      degree control (`R03`) and a representation-sensitive digest gate (`R07`).

  (iii) UNIVERSAL INTERFACE

      `R04` packages the raw table as a public artifact record `UC`, exposes
      evaluation semantics (`U_table`, `eval_poly_table`), and republishes the
      bounded profile metadata in one interface record `universal`.

  (iv) BOUNDED ENDPOINT

      `R08` defines the bounded theoremhood predicate `Bounded_Thm_k` and proves
      the table-level endpoint theorem: bounded theoremhood is equivalent to the
      existence of an environment satisfying the pinned input encoding,
      the representation bound, and the cubic equation.

  (v) EFFECTIVITY CHECKS

      `R05` contains executable sanity checks over the fixed artifact. These are
      not the undecidability content of the larger project family; they are only
      finite validation facts for this one bounded table.
*)

(*************************************************************************)
(*                                                                       *)
(*                    ARTIFACT METADATA AND INPUT PINNING                *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  COEFFICIENT TABLE METADATA
*)

Definition audit_monom : Type :=
  monom.

Definition audit_var_count : nat :=
  var_count.

Definition audit_base : Z :=
  base.

Definition audit_channel_count : nat :=
  channel_count.

Definition audit_bound_n_lines : nat :=
  bound_n_lines.

Definition audit_bound_digit_width : nat :=
  bound_digit_width.

Definition audit_bound_max_repr_lane : nat :=
  bound_max_repr_lane.

Definition audit_bound_max_repr_full : nat :=
  bound_max_repr_full.

Definition audit_expected_max_degree : nat :=
  expected_max_degree.

Definition audit_expected_has_degree_3 : bool :=
  expected_has_degree_3.

Definition audit_expected_count_degree_3_monomials : nat :=
  expected_count_degree_3_monomials.

Definition audit_encoding_scheme : string :=
  encoding_scheme.

Definition audit_pairing_layout : string :=
  pairing_layout.

Definition audit_successor_scheme : string :=
  successor_scheme.

Definition audit_debug_nonadjacency_disabled : bool :=
  debug_nonadjacency_disabled.

Definition audit_max_coeff_digits : nat :=
  max_coeff_digits.

Definition audit_coeff_hash : string :=
  coeff_hash.

(*
  (ii)
  PUBLIC INPUT PINNING
*)

Definition audit_ix_u : nat :=
  ix_u.

Definition audit_var_u : string :=
  var_u.

Definition audit_ix_u_lt_var_count :
  (audit_ix_u < audit_var_count)%nat :=
  ix_u_lt_var_count.

Definition audit_public_var_indices : list (string * nat) :=
  public_var_indices.

(*************************************************************************)
(*                                                                       *)
(*                    TABLE SEMANTICS, DEGREE, AND DIGEST                *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  RAW TABLE AND EVALUATION
*)

Definition audit_poly : list audit_monom :=
  poly.

Definition audit_eval_monom :
  (nat -> Z) -> audit_monom -> Z :=
  eval_monom.

(*
  Raw coefficient-table evaluator, before the interface aliasing in `R04`.
*)

Definition audit_U_raw : (nat -> Z) -> Z :=
  R02__Coefficients.U.

(*
  (ii)
  DEGREE CERTIFICATION
*)

Definition audit_sum_exps : list (nat * nat) -> nat :=
  sum_exps.

Definition audit_exps_ok : list (nat * nat) -> bool :=
  exps_ok.

Definition audit_monom_deg_ok : audit_monom -> bool :=
  monom_deg_ok.

Definition audit_poly_deg_ok : list audit_monom -> bool :=
  poly_deg_ok.

Definition audit_deg_ok : bool :=
  deg_ok.

Definition audit_degree_le_3 :
  audit_deg_ok = true :=
  degree_le_3.

Definition audit_monom_degree : audit_monom -> nat :=
  monom_degree.

Definition audit_degrees : list nat :=
  degrees.

Definition audit_max_degree : nat :=
  max_degree.

Definition audit_has_degree_3 : bool :=
  has_degree_3.

Definition audit_count_degree_3 : nat :=
  count_degree_3.

Definition audit_max_degree_eq_3 :
  audit_max_degree = 3%nat :=
  max_degree_eq_3.

Definition audit_has_degree_3_true :
  audit_has_degree_3 = true :=
  has_degree_3_true.

Definition audit_degree_at_most_3 :
  (audit_max_degree <= 3)%nat :=
  degree_at_most_3.

(*
  (iii)
  DIGEST GATE
*)

Definition audit_digest_modulus : Z :=
  digest_modulus.

Definition audit_digest_mul_exps : Z :=
  digest_mul_exps.

Definition audit_digest_mul_monom : Z :=
  digest_mul_monom.

Definition audit_digest_mul_table : Z :=
  digest_mul_table.

Definition audit_encode_ve : nat * nat -> Z :=
  encode_ve.

Definition audit_encode_exps : list (nat * nat) -> Z :=
  encode_exps.

Definition audit_encode_monom : audit_monom -> Z :=
  encode_monom.

Definition audit_digest_step : Z -> audit_monom -> Z :=
  digest_step.

Definition audit_table_digest_of : list audit_monom -> Z :=
  table_digest_of.

Definition audit_table_digest : Z :=
  table_digest.

Definition audit_table_digest_expected : Z :=
  table_digest_expected.

Definition audit_table_digest_ok :
  audit_table_digest = audit_table_digest_expected :=
  table_digest_ok.

(*************************************************************************)
(*                                                                       *)
(*                         UNIVERSAL INTERFACE                           *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  ENVIRONMENT AND TABLE-LEVEL EVALUATION
*)

Definition audit_env : Type :=
  env.

Definition audit_U_table : audit_env -> Z :=
  U_table.

Definition audit_U : audit_env -> Z :=
  R04__Universal.U.

Definition audit_eval_poly_table : audit_env -> Z :=
  eval_poly_table.

Definition audit_eval_poly : audit_env -> Z :=
  eval_poly.

Definition audit_bounded_n_lines : nat :=
  bounded_n_lines.

Definition audit_bounded_digit_width : nat :=
  bounded_digit_width.

Definition audit_bounded_max_repr_lane : nat :=
  bounded_max_repr_lane.

Definition audit_bounded_max_repr_full : nat :=
  bounded_max_repr_full.

Definition audit_cubic_sat_env : audit_env -> Prop :=
  cubic_sat_env.

Definition audit_env_nonneg : audit_env -> Prop :=
  env_nonneg.

Definition audit_cubic_sat_env_N : audit_env -> Prop :=
  cubic_sat_env_N.

Definition audit_cubic_sat_list : list Z -> Prop :=
  cubic_sat_list.

Definition audit_cubic_sat_list_N : list Z -> Prop :=
  cubic_sat_list_N.

Definition audit_cubic_sat_list_env :
  forall xs,
    audit_cubic_sat_list xs ->
    audit_cubic_sat_env (fun i => nth_default 0%Z xs i) :=
  cubic_sat_list_env.

Definition audit_cubic_sat_list_N_env :
  forall xs,
    audit_cubic_sat_list_N xs ->
    audit_cubic_sat_env_N (fun i => nth_default 0%Z xs i) :=
  cubic_sat_list_N_env.

Definition audit_cubic_degree_le_3 :
  audit_deg_ok = true :=
  cubic_degree_le_3.

(*
  (ii)
  PACKAGED ARTIFACT RECORDS
*)

Definition audit_universal_cubic_artifact : Type :=
  UniversalCubic.

Definition audit_UC : audit_universal_cubic_artifact :=
  UC.

Definition audit_universal_metadata : Type :=
  universal_cubic.

Definition audit_universal : audit_universal_metadata :=
  universal.

Definition audit_U_degree_3 :
  audit_deg_ok = true :=
  U_degree_3.

(*************************************************************************)
(*                                                                       *)
(*                     EFFECTIVITY AND BOUNDED ENDPOINT                  *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  EFFECTIVITY CHECKS OVER THE FIXED ARTIFACT
*)

Definition audit_zero_env : audit_env :=
  zero_env.

Definition audit_var_index_okb : list (nat * nat) -> bool :=
  var_index_okb.

Definition audit_monom_index_okb : audit_monom -> bool :=
  monom_index_okb.

Definition audit_poly_index_okb : list audit_monom -> bool :=
  poly_index_okb.

Definition audit_coeffs_nonzero : list audit_monom -> bool :=
  coeffs_nonzero.

Definition audit_poly_nonempty : bool :=
  poly_nonempty.

Definition audit_test_eval_zero_env_computable :
  exists z, audit_eval_poly_table audit_zero_env = z :=
  test_eval_zero_env_computable.

Definition audit_test_eval_deterministic :
  forall rho, audit_eval_poly_table rho = audit_eval_poly_table rho :=
  test_eval_deterministic.

Definition audit_test_eval_small_env :
  let rho :=
    fun i =>
      match i with
      | 0%nat => 1%Z
      | _ => 0%Z
      end in
  exists z, audit_eval_poly_table rho = z :=
  test_eval_small_env.

Definition audit_test_all_indices_bounded :
  audit_poly_index_okb audit_poly = true :=
  test_all_indices_bounded.

Definition audit_test_no_zero_monomials :
  audit_coeffs_nonzero audit_poly = true :=
  test_no_zero_monomials.

Definition audit_test_poly_nonempty :
  audit_poly_nonempty = true :=
  test_poly_nonempty.

Definition audit_test_degree_at_most_3 :
  (audit_max_degree <= 3)%nat :=
  test_degree_at_most_3.

Definition audit_test_max_degree_eq_3 :
  audit_max_degree = 3%nat :=
  test_max_degree_eq_3.

Definition audit_test_has_degree_3_true :
  audit_has_degree_3 = true :=
  test_has_degree_3_true.

(*
  (ii)
  BOUNDED ENDPOINT
*)

Definition audit_input_encoding_table :
  nat -> audit_env -> Prop :=
  InputEncoding_table.

Definition audit_representation_bound :
  audit_env -> Prop :=
  RepresentationBound.

Definition audit_bounded_thm_k : nat -> Prop :=
  Bounded_Thm_k.

Definition audit_bounded_universal_cubic :
  forall t,
    audit_bounded_thm_k t <->
    exists rho : audit_env,
      audit_input_encoding_table t rho /\
      audit_representation_bound rho /\
      audit_U_table rho = 0 :=
  bounded_universal_cubic.

Definition audit_bounded_endpoint_inspects_table :
  audit_table_digest_of (uc_poly audit_UC) = audit_table_digest_expected :=
  bounded_endpoint_inspects_table.

Definition audit_bounded_universal_cubic_endpoint :
  forall t,
    audit_table_digest_of (uc_poly audit_UC) = audit_table_digest_expected /\
    (audit_bounded_thm_k t <->
      exists rho : audit_env,
        audit_input_encoding_table t rho /\
        audit_representation_bound rho /\
        audit_U_table rho = 0) :=
  bounded_universal_cubic_endpoint.

Definition audit_t003_endpoint :
  forall t,
    audit_table_digest_of (uc_poly audit_UC) = audit_table_digest_expected /\
    (audit_bounded_thm_k t <->
      exists rho : audit_env,
        audit_input_encoding_table t rho /\
        audit_representation_bound rho /\
        audit_U_table rho = 0) :=
  bounded_universal_cubic_endpoint.

(*************************************************************************)
(*                                                                       *)
(*                                  QED                                  *)
(*                                                                       *)
(*                    Bounded Universal Cubic Endpoint                   *)
(*                                                                       *)
(*                             PROOF IN STEPS                            *)
(*                                                                       *)
(*    Step 1. Fix the generated coefficient table `audit_poly` together  *)
(*            with its pinned public-input index `audit_ix_u`.           *)
(*                                                                       *)
(*    Step 2. Certify the table structurally by two independent gates:   *)
(*            degree at most 3 and the representation-sensitive digest   *)
(*            identity `audit_table_digest = audit_table_digest_expected`. *)
(*                                                                       *)
(*    Step 3. Package the artifact as `audit_UC`, exposing both the      *)
(*            evaluator `audit_U_table` and the digest certificate.      *)
(*                                                                       *)
(*    Step 4. Define bounded theoremhood by existence of an environment  *)
(*            satisfying the pinned input encoding, the representation   *)
(*            bound, and the cubic equation.                             *)
(*                                                                       *)
(*    Step 5. Show that this bounded theoremhood predicate is exactly    *)
(*            the solvability predicate for the pinned table artifact.   *)
(*                                                                       *)
(*                             MECHANIZATION                             *)
(*                                                                       *)
(*    forall t,                                                          *)
(*      table_digest_of (uc_poly audit_UC) = audit_table_digest_expected *)
(*      /\                                                              *)
(*      (audit_bounded_thm_k t <->                                      *)
(*        exists rho : audit_env,                                       *)
(*          audit_input_encoding_table t rho /\                         *)
(*          audit_representation_bound rho /\                           *)
(*          audit_U_table rho = 0)                                      *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    For the fixed bounded artifact pinned in `T003`, a code `t`        *)
(*    satisfies the bounded theoremhood predicate exactly when there     *)
(*    exists an admissible environment whose public input slot encodes   *)
(*    `t` and whose evaluation makes the cubic table vanish.            *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is a bounded endpoint for one pinned cubic artifact. It is    *)
(*    not the claim that this single fixed table is already universal    *)
(*    for all theoremhood; the larger undecidability content belongs to  *)
(*    the scaling family, not to this one bounded instance.              *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.

Print Assumptions degree_le_3.
Print Assumptions table_digest_ok.
Print Assumptions bounded_universal_cubic.
Print Assumptions bounded_endpoint_inspects_table.
Print Assumptions bounded_universal_cubic_endpoint.
