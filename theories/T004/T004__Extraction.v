(* T004__Extraction.v *)

From Coq Require Import Arith Bool Extraction List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Phase_One
  R02__Phase_Two
  R03__Phase_Three
  R04__1st_Corollary.

Open Scope Z_scope.

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
(*    Proofcase / T004 -- OCaml Extraction Interface                     *)
(*                                                                       *)
(*    This  file  specifies  the  extraction  of the development into    *)
(*    OCaml.  It  records  how  executable code is generated from the    *)
(*    definitions  with  computational  content, while proof-specific    *)
(*    material  is erased during extraction. The resulting OCaml code    *)
(*    can then be inspected or executed independently of the original    *)
(*    proofs.                                                            *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
  (1)
  We encode a bit as a natural number for OCaml inspection.
*)

Definition bit_to_nat (b : bit) : nat :=
  if b then 1%nat else 0%nat.

(*
  (2)
  We encode a finite bit list as a natural-number list.
*)

Definition bit_list_to_nat_list (xs : list bit) : list nat :=
  map bit_to_nat xs.

(*
  (3)
  We extract the centered finite window of an arbitrary row.
*)

Definition row_window (r : row) (radius : nat) : list bit :=
  map r (centered_coords radius).

(*
  (4)
  We expose that centered row window in nat-coded form.
*)

Definition row_window_as_nat (r : row) (radius : nat) : list nat :=
  bit_list_to_nat_list (row_window r radius).

(*
  (5)
  We expose the canonical seed window.
*)

Definition seed_window (radius : nat) : list bit :=
  row_window seed_row radius.

(*
  (6)
  We expose the canonical seed window in nat-coded form.
*)

Definition seed_window_as_nat (radius : nat) : list nat :=
  row_window_as_nat seed_row radius.

(*
  (7)
  We expose a single canonical cell value.
*)

Definition canonical_value (t : nat) (x : Z) : bit :=
  canonical_row t x.

(*
  (8)
  We expose a single canonical cell value in nat-coded form.
*)

Definition canonical_value_as_nat (t : nat) (x : Z) : nat :=
  bit_to_nat (canonical_value t x).

(*
  (9)
  We expose a finite window cut from an arbitrary spacetime trajectory.
*)

Definition trajectory_window (u : space_time) (radius t : nat) : list bit :=
  window_data u radius t.

(*
  (10)
  We expose a trajectory window in nat-coded form.
*)

Definition trajectory_window_as_nat
    (u : space_time) (radius t : nat) : list nat :=
  bit_list_to_nat_list (trajectory_window u radius t).

(*
  (11)
  We expose a finite list of consecutive trajectory windows.
*)

Fixpoint trajectory_windows_from
    (u : space_time) (radius start len : nat) : list (list bit) :=
  match len with
  | 0%nat => []
  | S len' =>
      trajectory_window u radius start ::
      trajectory_windows_from u radius (S start) len'
  end.

(*
  (12)
  We expose the finite prefix of trajectory windows from time 0.
*)

Definition trajectory_prefix_windows
    (u : space_time) (radius height : nat) : list (list bit) :=
  trajectory_windows_from u radius 0%nat (S height).

(*
  (13)
  We expose the same trajectory prefix in nat-coded form.
*)

Definition trajectory_prefix_windows_as_nat
    (u : space_time) (radius height : nat) : list (list nat) :=
  map bit_list_to_nat_list (trajectory_prefix_windows u radius height).

(*
  (14)
  We expose the canonical centered window at time t.
*)

Definition canonical_window (radius t : nat) : list bit :=
  center_window radius t.

(*
  (15)
  We expose the canonical centered window in nat-coded form.
*)

Definition canonical_window_as_nat (radius t : nat) : list nat :=
  bit_list_to_nat_list (canonical_window radius t).

(*
  (16)
  We expose a finite canonical prefix of centered windows.
*)

Definition canonical_prefix_windows
    (radius height : nat) : list (list bit) :=
  trajectory_prefix_windows canonical_row radius height.

(*
  (17)
  We expose the same canonical prefix in nat-coded form.
*)

Definition canonical_prefix_windows_as_nat
    (radius height : nat) : list (list nat) :=
  trajectory_prefix_windows_as_nat canonical_row radius height.

(*
  (18)
  We expose windows from the canonically shifted trajectory.
*)

Definition shifted_canonical_window
    (period radius t : nat) : list bit :=
  trajectory_window (shifted_canonical_trajectory period) radius t.

(*
  (19)
  We expose shifted canonical windows in nat-coded form.
*)

Definition shifted_canonical_window_as_nat
    (period radius t : nat) : list nat :=
  bit_list_to_nat_list (shifted_canonical_window period radius t).

(*
  (20)
  We expose finite prefixes from the shifted canonical trajectory.
*)

Definition shifted_canonical_prefix_windows
    (period radius height : nat) : list (list bit) :=
  trajectory_prefix_windows (shifted_canonical_trajectory period) radius height.

(*
  (21)
  We expose those shifted prefixes in nat-coded form.
*)

Definition shifted_canonical_prefix_windows_as_nat
    (period radius height : nat) : list (list nat) :=
  trajectory_prefix_windows_as_nat
    (shifted_canonical_trajectory period) radius height.

(*
  (22)
  We expose the local seed-window model on a finite inspection radius.
*)

Definition local_seed_window_model_window
    (seed_radius window_radius : nat) : list bit :=
  row_window (local_seed_window_model seed_radius) window_radius.

(*
  (23)
  We expose the local seed-window model in nat-coded form.
*)

Definition local_seed_window_model_window_as_nat
    (seed_radius window_radius : nat) : list nat :=
  bit_list_to_nat_list
    (local_seed_window_model_window seed_radius window_radius).

(*
  (24)
  We expose a truncated canonical row on a finite inspection radius.
*)

Definition truncated_canonical_window
    (truncate_radius t window_radius : nat) : list bit :=
  row_window (truncate truncate_radius (canonical_row t)) window_radius.

(*
  (25)
  We expose the truncated canonical row in nat-coded form.
*)

Definition truncated_canonical_window_as_nat
    (truncate_radius t window_radius : nat) : list nat :=
  bit_list_to_nat_list
    (truncated_canonical_window truncate_radius t window_radius).

(*
  (26)
  We expose the finite replay radius used in the compactness route.
*)

Definition extracted_finite_replay_radius (n horizon : nat) : nat :=
  finite_replay_radius n horizon.

(*
  (27)
  Boolean equality on nat-coded finite windows.
*)

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => andb (Nat.eqb x y) (nat_list_eqb xs' ys')
  | _, _ => false
  end.

(*
  (28)
  Result type for the simple observational refuter.
*)

Inductive ObservedPeriodRefuterResult : Type :=
| Opr_invalid_period
| Opr_refuted :
    nat -> list nat -> list nat -> ObservedPeriodRefuterResult
| Opr_not_refuted_upto :
    nat -> ObservedPeriodRefuterResult.

(*
  (29)
  Nat-coded centered windows agree at time t and lag period.
*)

Definition observed_windows_match
    (radius period t : nat) : bool :=
  nat_list_eqb
    (canonical_window_as_nat radius t)
    (canonical_window_as_nat radius (t + period)%nat).

(*
  (30)
  Refutation object at a specific mismatch time.
*)

Definition observed_period_refutation_at
    (radius period t : nat) : ObservedPeriodRefuterResult :=
  Opr_refuted
    t
    (canonical_window_as_nat radius t)
    (canonical_window_as_nat radius (t + period)%nat).

(*
  (31)
  First observational mismatch from time t through the given horizon fuel.
*)

Fixpoint first_observed_period_refutation_from
    (radius period t fuel : nat) : option ObservedPeriodRefuterResult :=
  if observed_windows_match radius period t
  then
    match fuel with
    | 0%nat => None
    | S fuel' =>
        first_observed_period_refutation_from radius period (S t) fuel'
    end
  else Some (observed_period_refutation_at radius period t).

(*
  (32)
  Simple finite observational refuter.

  A returned refutation is honest finite evidence against the proposed
  period.  A non-refutation only says that no mismatch was found within
  the supplied finite horizon.
*)

Definition refute_observed_period
    (radius period horizon : nat) : ObservedPeriodRefuterResult :=
  if Nat.eqb period 0%nat
  then Opr_invalid_period
  else
    match first_observed_period_refutation_from radius period 0%nat horizon with
    | Some result => result
    | None => Opr_not_refuted_upto horizon
    end.

(*
  (33)
  Input object for the bounded uniform-tail witness checker.
*)

Record UniformTailWitnessCandidate : Type := {
  utwc_radius : nat;
  utwc_start : nat;
  utwc_period : nat;
  utwc_extra_bound : nat;
  utwc_time_bound : nat
}.

(*
  (34)
  Result type for the bounded uniform-tail witness checker.
*)

Inductive UniformTailWitnessCheck : Type :=
| Utwc_invalid_period
| Utwc_rejected :
    nat -> nat -> list nat -> list nat -> UniformTailWitnessCheck
| Utwc_accepts_through :
    nat -> nat -> UniformTailWitnessCheck.

(*
  (35)
  Nat-coded window at one point of the bounded witness obligation grid.
*)

Definition uniform_tail_window_as_nat
    (candidate : UniformTailWitnessCandidate)
    (extra t lag : nat) : list nat :=
  canonical_window_as_nat
    (utwc_radius candidate + extra)%nat
    (utwc_start candidate + t + lag)%nat.

(*
  (36)
  One bounded witness obligation holds at (extra, t).
*)

Definition uniform_tail_witness_matches
    (candidate : UniformTailWitnessCandidate)
    (extra t : nat) : bool :=
  nat_list_eqb
    (uniform_tail_window_as_nat candidate extra t 0%nat)
    (uniform_tail_window_as_nat candidate extra t (utwc_period candidate)).

(*
  (37)
  First rejection object at one failed witness obligation.
*)

Definition uniform_tail_witness_rejection
    (candidate : UniformTailWitnessCandidate)
    (extra t : nat) : UniformTailWitnessCheck :=
  Utwc_rejected
    extra
    t
    (uniform_tail_window_as_nat candidate extra t 0%nat)
    (uniform_tail_window_as_nat candidate extra t (utwc_period candidate)).

(*
  (38)
  Scan one fixed extra-radius layer for the first failed witness time.
*)

Fixpoint first_uniform_tail_time_failure
    (candidate : UniformTailWitnessCandidate)
    (extra t fuel : nat) : option UniformTailWitnessCheck :=
  if uniform_tail_witness_matches candidate extra t
  then
    match fuel with
    | 0%nat => None
    | S fuel' =>
        first_uniform_tail_time_failure candidate extra (S t) fuel'
    end
  else Some (uniform_tail_witness_rejection candidate extra t).

(*
  (39)
  Scan all bounded extra-radius layers for the first failed witness obligation.
*)

Fixpoint first_uniform_tail_extra_failure
    (candidate : UniformTailWitnessCandidate)
    (extra fuel : nat) : option UniformTailWitnessCheck :=
  match first_uniform_tail_time_failure
          candidate extra 0%nat (utwc_time_bound candidate) with
  | Some failure => Some failure
  | None =>
      match fuel with
      | 0%nat => None
      | S fuel' =>
          first_uniform_tail_extra_failure candidate (S extra) fuel'
      end
  end.

(*
  (40)
  Best-practice bounded witness checker.

  A rejection means that the supplied witness candidate fails the checked
  uniform-tail obligations.  Acceptance is explicitly bounded by the
  supplied extra/time limits carried by the candidate.
*)

Definition check_uniform_tail_witness_candidate
    (candidate : UniformTailWitnessCandidate) : UniformTailWitnessCheck :=
  if Nat.eqb (utwc_period candidate) 0%nat
  then Utwc_invalid_period
  else
    match first_uniform_tail_extra_failure
            candidate 0%nat (utwc_extra_bound candidate) with
    | Some failure => failure
    | None =>
        Utwc_accepts_through
          (utwc_extra_bound candidate)
          (utwc_time_bound candidate)
    end.

End Extraction_Interface.

Set Extraction Output Directory "T004_Extraction".
Extraction Language OCaml.

Extraction "UniformTailWitnessChecker.ml"
  bit_to_nat
  bit_list_to_nat_list
  canonical_window_as_nat
  check_uniform_tail_witness_candidate.

Extraction "ObservedPeriodRefuter.ml"
  bit_to_nat
  bit_list_to_nat_list
  canonical_window_as_nat
  refute_observed_period.

(*
  The  extraction surface above is purely computational. The commands below 
  print  only  the  main  theorem endpoints and the  remaining explicit open
  assumptions, so the build output stays readable.
*)

(*************************************************************************)
(*                                                                       *)
(*                               ENDPOINT                                *)
(*                                                                       *)
(*  Compactness-conditional Phase 1 corollary.                           *)
(*                                                                       *)
(*    replay_compactness_principle ->                                    *)
(*      forall n, ~ purely_periodic_center_window n                      *)
(*                                                                       *)
(*  This  is  part of the package, but it is not the preferred semantic  *)
(*  interface when discussing faithful realizers.                        *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions the_fall.
Print Assumptions no_pure_periodicity_of_centered_windows.
Print Assumptions center_strip_not_purely_periodic.

(*************************************************************************)
(*                                                                       *)
(*                               ENDPOINT                                *)
(*                                                                       *)
(*  Original Sin Theorem.                                                *)
(*                                                                       *)
(*    original_sin_theorem                                               *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions original_sin_theorem.

(*************************************************************************)
(*                                                                       *)
(*                               ENDPOINT                                *)
(*                                                                       *)
(*  The  direct  endpoint  states that no uniform periodic tail exists.  *)
(*  The  realizability  theorems printed below are packaged corollaries  *)
(*  of that stronger statement.                                          *)
(*                                                                       *)
(*  This is the preferred semantic endpoint for the package.             *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions uniformly_eventually_periodic_from_impossible.
Print Assumptions realizable_observational_periodic_tail_from_impossible.
Print Assumptions realizable_uniform_periodic_tail_from_impossible.

(*************************************************************************)
(*                                                                       *)
(*                               ENDPOINT                                *)
(*                                                                       *)
(*  Under  the  Faithfulness  Hypothesis,  eventual                      *)
(*  periodicity  of  centered windows is excluded. This is the cleanest  *)
(*  assumption-isolating wrapper exported by the package.                *)
(*                                                                       *)
(*  The  non-closed  ingredients  appear  as  explicit theorem premises  *)
(*  rather than hidden global axioms on the live package surface.        *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions classical_semantics_excludes_eventual_periodic_windows.
Print Assumptions classical_semantics_excludes_any_eventual_periodic_window.
