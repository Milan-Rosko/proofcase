(* T004_Proof.v *)

From Coq Require Import List ZArith.
Import ListNotations.

From T004 Require Import
  R00__Base
  R01__Seed
  R02__Local_Lemmas
  R03__Periodicity
  R04__Center_No_Pure_Periodicity
  R05__Glitch_Compactness
  R06__Mixed_Periodicity
  R07__Classic_Semantics.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  This file serves as the proof-theoretic synopsis of T004.  It        *)
(*  introduces no new mathematical content.  Rather, it organizes the    *)
(*  derivational architecture of the development and re-exports its      *)
(*  principal objects, interfaces, and endpoint theorems in a single     *)
(*  module.                                                              *)
(*                                                                       *)
(*  T004 is organized into four tracks.                                  *)
(*                                                                       *)
(*    1. The Phase 1 compactness corollary:                              *)
(*                                                                       *)
(*         replay_compactness_principle ->                               *)
(*           forall n, ~ purely_periodic_center_window n                 *)
(*                                                                       *)
(*       This uses bounded replay and Original Sin under an explicit     *)
(*       compactness premise.                                            *)
(*                                                                       *)
(*    2. The reverse-side syntactic route in R05.                        *)
(*                                                                       *)
(*       This contains closed local theorems about seed return,          *)
(*       support shells, bounded seed-window realizations, and the       *)
(*       first obligation-compactification pressure.  Its principal      *)
(*       Phase 2 endpoint is the bounded cutoff theorem:                 *)
(*                                                                       *)
(*         every_cutoff_still_remembers_seed.                            *)
(*                                                                       *)
(*       A separate hidden-support descent vocabulary remains in R05,    *)
(*       but it is not used by the live package interface.               *)
(*                                                                       *)
(*    3. The initial Phase 3 bridge in R06.                              *)
(*                                                                       *)
(*       This packages eventual periodicity as an infinite family        *)
(*       of repeated local predecessor problems at one fixed cutoff      *)
(*       phase.  Its strong semantic endpoint states that no faithful    *)
(*       uniform periodic tail exists.  The unresolved issue is the      *)
(*       bridge from bare fixed-width observation to that stronger       *)
(*       semantic notion.                                                *)
(*                                                                       *)
(*    4. The external classical corollary layer in R07.                  *)
(*                                                                       *)
(*       This packages what follows under a single external semantic     *)
(*       faithfulness premise.                                           *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                             PHASE ONE                                 *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  (1)
  Canonical single-seed initial row.
*)

Definition audit_seed_row : row :=
  seed_row.

(*
  (2)
  Canonical Rule 30 trajectory generated from the seed.
*)

Definition audit_canonical_row : nat -> row :=
  canonical_row.

(*
  (3)
  Centered finite window cut from the canonical trajectory.
*)

Definition audit_center_window : nat -> nat -> list bit :=
  center_window.

(*
  (4)
  One-bit center strip extracted from the canonical trajectory.
*)

Definition audit_center_strip : nat -> bit :=
  center_strip.

(*
  (5)
  Pure periodicity predicate for the centered window.
*)

Definition audit_purely_periodic_center_window : nat -> Prop :=
  purely_periodic_center_window.

(*
  (6)
  Bounded seed-window realization predicate used in Phase 2.
*)

Definition audit_local_seed_window_realization : nat -> row -> Prop :=
  local_seed_window_realization.

(*
  (7)
  Progenitor relation between predecessor rows and outputs.
*)

Definition audit_progenitor : row -> row -> Prop :=
  progenitor.

(*
  (8)
  Original Sin.
*)

Definition audit_original_sin :
  ~ exists u, progenitor u seed_row :=
  original_sin.

(*************************************************************************)
(*                                                                       *)
(*  No Progenitor Theorem                                                *)
(*                                                                       *)
(*  Term                                                                 *)
(*                                                                       *)
(*    ~ exists u, progenitor u seed_row                                  *)
(*                                                                       *)
(*  Syntactic content.                                                   *)
(*                                                                       *)
(*    There is no finitely supported row u whose one-step Rule 30 image  *)
(*    is exactly the centered seed row.                                  *)
(*                                                                       *)
(*  Semantic reading.                                                    *)
(*                                                                       *)
(*    The single seeded defect cannot be created in one forward step by  *)
(*    a finitely supported predecessor.  The seed has no progenitor.     *)
(*                                                                       *)
(*  Qualification.                                                       *)
(*                                                                       *)
(*    This theorem is compiled and closed under the global context.      *)
(*    It is the rigid local obstruction later used by both the           *)
(*    compactness route and the bounded cutoff-memory route.             *)
(*                                                                       *)
(*************************************************************************)

(*
  (9)
  Every canonical row is finitely supported.
*)

Definition audit_canonical_row_finitely_supported :
  forall t,
    finitely_supported (canonical_row t) :=
  canonical_row_finitely_supported.

(*
  (10)
  Light-cone vanishing outside canonical support.
*)

Definition audit_canonical_row_outside_light_cone :
  forall t x,
    (Z.of_nat t < Z.abs x)%Z ->
    canonical_row t x = false :=
  canonical_row_outside_light_cone.

(*
  (11)
  The left edge of the canonical cone is always hot.
*)

Definition audit_canonical_row_left_edge_true :
  forall t,
    canonical_row t (- Z.of_nat t)%Z = true :=
  canonical_row_left_edge_true.

(*
  (12)
  Pointwise non-repetition of the canonical orbit at positive lag.
*)

Definition audit_canonical_row_no_repetition_pointwise :
  forall t p,
    (0 < p)%nat ->
    exists x,
      canonical_row (t + p)%nat x <> canonical_row t x :=
  canonical_row_no_repetition_pointwise.

(*
  (13)
  The canonical trajectory never returns to the seed at positive time.
*)

Definition audit_canonical_row_successor_not_seed :
  forall t,
    canonical_row (S t) <> seed_row :=
  canonical_row_successor_not_seed.

(*
  (14)
  Window data extracted from an arbitrary spacetime tableau.
*)

Definition audit_window_data : space_time -> nat -> nat -> list bit :=
  window_data.

(*
  (15)
  Finite replay radius attached to each horizon.
*)

Definition audit_finite_replay_radius : nat -> nat -> nat :=
  finite_replay_radius.

(*
  (16)
  Finite replay problem used by the compactness route.
*)

Definition audit_finite_replay_problem : nat -> nat -> Prop :=
  finite_replay_problem.

(*
  (17)
  The local seed-window predecessor problem is always satisfiable.
*)

Definition audit_local_seed_window_predecessor_is_always_satisfiable :
  forall R,
    local_seed_window_predecessor R :=
  local_seed_window_predecessor_is_always_satisfiable.

(*
  (18)
  Pure periodicity yields finite replay at every horizon.
*)

Definition audit_purely_periodic_implies_finite_replay_problem :
  forall n horizon,
    audit_purely_periodic_center_window n ->
    audit_finite_replay_problem n horizon :=
  purely_periodic_implies_finite_replay_problem.

(*
  (19)
  Upward admissibility as the infinite replay object.
*)

Definition audit_upward_admissible : nat -> Prop :=
  upward_admissible.

(*
  (20)
  Compactness premise turning all finite replay data into admissibility.
*)

Definition audit_replay_compactness_principle : Prop :=
  replay_compactness_principle.

(*
  (21)
  Candidate rows sitting above the seed in an admissible replay.
*)

Definition audit_candidate_above_seed : row -> Prop :=
  candidate_above_seed.

(*
  (22)
  Admissibility produces such a candidate row.
*)

Definition audit_upward_admissibility_implies_candidate_row :
  forall n,
    audit_upward_admissible n ->
    exists u, audit_candidate_above_seed u :=
  upward_admissibility_implies_candidate_row.

(*
  (23)
  Every candidate row steps exactly to the seed.
*)

Definition audit_candidate_row_respects_step :
  forall u,
    audit_candidate_above_seed u ->
    forall x,
      step u x = seed_row x :=
  candidate_row_respects_step.

(*
  (24)
  Every admissible candidate row has finite support.
*)

Definition audit_candidate_row_has_finite_support :
  forall u,
    audit_candidate_above_seed u ->
    finitely_supported u :=
  candidate_row_has_finite_support.

(*
  (25)
  Every admissible candidate row is a progenitor of the seed.
*)

Definition audit_candidate_row_is_progenitor :
  forall u,
    audit_candidate_above_seed u ->
    progenitor u seed_row :=
  candidate_row_is_progenitor.

(*
  (26)
  Admissibility forces the seed to have a progenitor.
*)

Definition audit_upward_admissibility_implies_seed_has_progenitor :
  forall n,
    audit_upward_admissible n ->
    exists u, progenitor u seed_row :=
  upward_admissibility_implies_seed_has_progenitor.

(*
  (27)
  Contradiction packaged with periodic observation and upward admissibility.
*)

Definition audit_observable_periodicity_plus_upward_admissibility_contradict :
  forall n,
    audit_purely_periodic_center_window n ->
    audit_upward_admissible n ->
    False :=
  observable_periodicity_plus_upward_admissibility_contradict.

(*
  (28)
  Under the compactness premise, Original Sin and classical nonadmissibility
  yield a finite replay obstruction.
*)

Definition audit_original_sin_implies_finite_replay_obstruction :
  audit_replay_compactness_principle ->
  forall n,
    exists horizon, ~ audit_finite_replay_problem n horizon :=
  original_sin_implies_finite_replay_obstruction.

(*
  (29)
  Phase 1 compactness corollary: no centered window is purely periodic.
*)

Definition audit_no_pure_periodicity_of_centered_windows :
  audit_replay_compactness_principle ->
  forall n,
    ~ audit_purely_periodic_center_window n :=
  no_pure_periodicity_of_centered_windows.

(*
  (30)
  Width-zero instance of the same compactness corollary.
*)

Definition audit_center_strip_not_purely_periodic :
  audit_replay_compactness_principle ->
  ~ audit_purely_periodic_center_window 0%nat :=
  center_strip_not_purely_periodic.

(*
  (31)
  Canonical audit alias for the Phase 1 compactness corollary.
*)

Definition audit_phase1_endpoint :
  audit_replay_compactness_principle ->
  forall n,
    ~ audit_purely_periodic_center_window n :=
  no_pure_periodicity_of_centered_windows.

(*************************************************************************)
(*                                                                       *)
(*  No Pure Periodicity Theorem                                          *)
(*                                                                       *)
(*  Term                                                                 *)
(*                                                                       *)
(*    replay_compactness_principle ->                                    *)
(*      forall n, ~ purely_periodic_center_window n                      *)
(*                                                                       *)
(*  Syntactic content.                                                   *)
(*                                                                       *)
(*    Under the compactness premise, every finite observation radius n   *)
(*    has the property that the centered width-(2n+1) window of the      *)
(*    seeded Rule 30 evolution fails to be purely periodic from time 0.  *)
(*                                                                       *)
(*  Semantic reading.                                                    *)
(*                                                                       *)
(*    If every finitely satisfiable replay problem extended to a full     *)
(*    admissible replay, then any putative pure centered periodicity     *)
(*    would force the seed into the forbidden interior configuration.    *)
(*    Hence pure centered periodicity is excluded under that premise.    *)
(*                                                                       *)
(*  Qualification.                                                       *)
(*                                                                       *)
(*    This is an explicit compactness-conditional corollary assembled    *)
(*    in R04 from bounded replay, the compactness premise, and          *)
(*    Original Sin.                                                      *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                             PHASE TWO                                 *)
(*                                                                       *)
(*************************************************************************)

(*
  (32)
  We define truncation to a bounded radius.
*)

Definition audit_truncate : nat -> row -> row :=
  truncate.

(*
  (33)
  We define the canonical bounded-time seeded prefix predicate.
*)

Definition audit_seeded_prefix : nat -> space_time -> Prop :=
  seeded_prefix.

(*
  (34)
  We define the canonical trajectory shifted in time.
*)

Definition audit_shifted_canonical_trajectory : nat -> space_time :=
  shifted_canonical_trajectory.

(*
  (35)
  We define repetition of a seeded prefix after a lag.
*)

Definition audit_seeded_prefix_repeats_after : nat -> nat -> Prop :=
  seeded_prefix_repeats_after.

(*
  (36)
  We record that repeated seeded prefixes force literal seed return.
*)

Definition audit_seeded_prefix_repeats_after_implies_seed_return :
  forall h P,
    audit_seeded_prefix_repeats_after h P ->
    canonical_row P = seed_row :=
  seeded_prefix_repeats_after_implies_seed_return.

(*
  (37)
  We record that positive-period seeded-prefix repetition is impossible.
*)

Definition audit_seeded_prefix_repeats_after_positive_period_impossible :
  forall h P,
    (0 < P)%nat ->
    ~ audit_seeded_prefix_repeats_after h P :=
  seeded_prefix_repeats_after_positive_period_impossible.

(*
  (38)
  We record that a seed window cannot be realized inside too small a support.
*)

Definition audit_local_seed_window_realization_with_small_support_impossible :
  forall N u,
    (forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      u x = false) ->
    audit_local_seed_window_realization (S N) u ->
    False :=
  local_seed_window_realization_with_small_support_impossible.

(*
  (39)
  We record the support-bound version of the same cutoff impossibility.
*)

Definition audit_local_seed_window_realization_with_support_bound_impossible :
  forall R N u,
    (forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      u x = false) ->
    (S N <= R)%nat ->
    audit_local_seed_window_realization R u ->
    False :=
  local_seed_window_realization_with_support_bound_impossible.

(*
  (40)
  We define the four distinguished sites of the outer shell.
*)

Definition audit_outer_shell_site : Type :=
  outer_shell_site.

(*
  (41)
  We define the coordinate of each outer-shell site.
*)

Definition audit_outer_shell_coord : nat -> audit_outer_shell_site -> Z :=
  outer_shell_coord.

(*
  (42)
  We define nonemptiness of the outer shell.
*)

Definition audit_outer_shell_nonempty : nat -> row -> Prop :=
  outer_shell_nonempty.

(*
  (43)
  We define the four-bit outer-shell signature.
*)

Definition audit_outer_shell_signature : nat -> row -> list bit :=
  outer_shell_signature.

(*
  (44)
  We record that every seed-window realization emits outer-shell support.
*)

Definition audit_local_seed_window_realization_requires_outer_shell :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    exists x,
      (Z.of_nat N < Z.abs x <= Z.of_nat (S (S N)))%Z /\
      truncate (S (S N)) u x = true :=
  local_seed_window_realization_requires_outer_shell.

(*
  (45)
  We record the nonempty-shell reformulation of that emission fact.
*)

Definition audit_local_seed_window_realization_requires_outer_shell_nonempty :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_outer_shell_nonempty N u :=
  local_seed_window_realization_requires_outer_shell_nonempty.

(*
  (46)
  We record that the emitted shell signature is never the all-zero signature.
*)

Definition audit_local_seed_window_realization_requires_nonzero_shell_signature :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_outer_shell_signature N u <> [false; false; false; false] :=
  local_seed_window_realization_requires_nonzero_shell_signature.

(*
  (47)
  We define the finite shell-obligation type.
*)

Definition audit_shell_obligation : Type :=
  shell_obligation.

(*
  (48)
  We define realization of the left shell obligation.
*)

Definition audit_realizes_left_shell_obligation :
  nat -> row -> Prop :=
  realizes_left_shell_obligation.

(*
  (49)
  We define realization of the right shell obligation.
*)

Definition audit_realizes_right_shell_obligation :
  nat -> row -> Prop :=
  realizes_right_shell_obligation.

(*
  (50)
  We define realization of a shell obligation in general.
*)

Definition audit_realizes_shell_obligation :
  nat -> row -> audit_shell_obligation -> Prop :=
  realizes_shell_obligation.

(*
  (51)
  We define the far-left hotness predicate.
*)

Definition audit_far_left_hot : nat -> row -> Prop :=
  far_left_hot.

(*
  (52)
  We define the inner-right hotness predicate.
*)

Definition audit_inner_right_hot : nat -> row -> Prop :=
  inner_right_hot.

(*
  (53)
  We define the right edge zero equation.
*)

Definition audit_right_edge_zero_equation : nat -> row -> Prop :=
  right_edge_zero_equation.

(*
  (54)
  We define the left edge zero equation.
*)

Definition audit_left_edge_zero_equation : nat -> row -> Prop :=
  left_edge_zero_equation.

(*
  (55)
  We record that seed-window realization forces the right edge equation.
*)

Definition audit_right_edge_zero_equation_from_seed_window :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_right_edge_zero_equation N u :=
  right_edge_zero_equation_from_seed_window.

(*
  (56)
  We record that seed-window realization forces the left edge equation.
*)

Definition audit_left_edge_zero_equation_from_seed_window :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_left_edge_zero_equation N u :=
  left_edge_zero_equation_from_seed_window.

(*
  (57)
  We unfold the right edge equation into its explicit inclusive-OR
  obligation.
*)

Definition audit_right_edge_zero_equation_unfolds_to_or_obligation :
  forall N u,
    audit_right_edge_zero_equation N u ->
    truncate (S (S N)) u (Z.of_nat N) =
      orb (outer_shell_value N u outer_right)
          (outer_shell_value N u outer_far_right) :=
  right_edge_zero_equation_unfolds_to_xor_obligation.

(*
  (58)
  We unfold the left edge equation into its explicit inclusive-OR
  obligation.
*)

Definition audit_left_edge_zero_equation_unfolds_to_or_obligation :
  forall N u,
    audit_left_edge_zero_equation N u ->
    outer_shell_value N u outer_far_left =
      orb (outer_shell_value N u outer_left)
          (truncate (S (S N)) u (- Z.of_nat N)) :=
  left_edge_zero_equation_unfolds_to_xor_obligation.

(*
  (59)
  We record that every seed-window realization emits a left or right shell obligation.
*)

Definition audit_local_seed_window_realization_emits_shell_obligation :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_realizes_shell_obligation N u obligation_left \/
    audit_realizes_shell_obligation N u obligation_right :=
  local_seed_window_realization_emits_shell_obligation.

(*
  (60)
  We record that the left shell obligation, under the left edge equation,
  forces far-left pressure.
*)

Definition audit_left_shell_obligation_forces_far_left_hot :
  forall N u,
    audit_left_edge_zero_equation N u ->
    audit_realizes_left_shell_obligation N u ->
    audit_far_left_hot N u :=
  left_shell_obligation_forces_far_left_hot.

(*
  (61)
  We record that the right shell obligation forces inner-right pressure.
*)

Definition audit_right_shell_obligation_forces_inner_right_hot :
  forall N u,
    audit_right_edge_zero_equation N u ->
    audit_realizes_right_shell_obligation N u ->
    audit_inner_right_hot N u :=
  right_shell_obligation_forces_inner_right_hot.

(*
  (62)
  We record the first shell dichotomy: far-left persistence or inner-right pressure.
*)

Definition audit_local_seed_window_realization_forces_far_left_or_inner_right :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_far_left_hot N u \/ audit_inner_right_hot N u :=
  local_seed_window_realization_forces_far_left_or_inner_right.

(*
  (63)
  We record that inner-right pressure compactifies to a smaller right obligation.
*)

Definition audit_inner_right_hot_compactifies_to_smaller_right_obligation :
  forall N u,
    audit_inner_right_hot (S N) u ->
    audit_realizes_right_shell_obligation N u :=
  inner_right_hot_compactifies_to_smaller_right_obligation.

(*
  (64)
  We record the first compactification dichotomy at the next radius.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_or_right_compactification :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_far_left_hot (S N) u \/ audit_realizes_right_shell_obligation N u :=
  local_seed_window_realization_forces_left_persistence_or_right_compactification.

(*
  (65)
  We record one-step compactification of a right shell obligation.
*)

Definition audit_right_shell_obligation_compactifies_one_step :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_realizes_right_shell_obligation (S N) u ->
    audit_realizes_right_shell_obligation N u :=
  right_shell_obligation_compactifies_one_step.

(*
  (66)
  We record many-step compactification of a right shell obligation.
*)

Definition audit_right_shell_obligation_compactifies_to_smaller_radius :
  forall k m u,
    audit_local_seed_window_realization (S (S (k + m))) u ->
    audit_realizes_right_shell_obligation (k + m) u ->
    audit_realizes_right_shell_obligation k u :=
  right_shell_obligation_compactifies_to_smaller_radius.

(*
  (67)
  We record the core compactification dichotomy.
*)

Definition audit_local_seed_window_realization_either_left_persists_or_right_compactifies_to_core :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_far_left_hot (S N) u \/ audit_realizes_right_shell_obligation 0 u :=
  local_seed_window_realization_either_left_persists_or_right_compactifies_to_core.

(*
  (68)
  We record the core compactification theorem under failure of left persistence.
*)

Definition audit_local_seed_window_realization_without_left_persistence_compactifies_right_to_core :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    ~ audit_far_left_hot (S N) u ->
    audit_realizes_right_shell_obligation 0 u :=
  local_seed_window_realization_without_left_persistence_compactifies_right_to_core.

(*
  (69)
  We record that a core right obligation, under radius-two seed-window
  realization, forces left pressure at radius one.
*)

Definition audit_right_shell_obligation_at_core_forces_far_left_hot_one :
  forall u,
    audit_local_seed_window_realization 2 u ->
    audit_realizes_right_shell_obligation 0 u ->
    audit_far_left_hot 1 u :=
  right_shell_obligation_at_core_forces_far_left_hot_one.

(*
  (70)
  We record the radius-two corollary of that core pressure theorem.
*)

Definition audit_local_seed_window_realization_radius_two_forces_far_left_hot_one :
  forall u,
    audit_local_seed_window_realization 2 u ->
    audit_far_left_hot 1 u :=
  local_seed_window_realization_radius_two_forces_far_left_hot_one.

(*
  (71)
  We define bounded avoidance of left pressure up to level N.
*)

Definition audit_bounded_right_avoidance_chain :
  nat -> row -> Prop :=
  bounded_right_avoidance_chain.

(*
  (72)
  We record that bounded right avoidance is impossible.
*)

Definition audit_bounded_right_avoidance_chain_impossible :
  forall N u,
    audit_bounded_right_avoidance_chain N u ->
    False :=
  bounded_right_avoidance_chain_impossible.

(*
  (73)
  We record a constructive extraction of a left-persistence level.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_level :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    {k : nat | (k <= N)%nat /\ audit_far_left_hot (S k) u} :=
  local_seed_window_realization_forces_left_persistence_level.

(*
  (74)
  We record the existential version of that left-persistence extraction.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_somewhere :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    exists k,
      (k <= N)%nat /\ audit_far_left_hot (S k) u :=
  local_seed_window_realization_forces_left_persistence_somewhere.

(*
  (75)
  We define the bounded left-obligation site type.
*)

Definition audit_bounded_left_obligation_site :
  nat -> Type :=
  bounded_left_obligation_site.

(*
  (76)
  We define the coordinate attached to a bounded left-obligation site.
*)

Definition audit_bounded_left_obligation_coord :
  forall N,
    audit_bounded_left_obligation_site N -> Z :=
  @bounded_left_obligation_coord.

(*
  (77)
  We define the bounded obligation replay object.
*)

Definition audit_bounded_obligation_replay :
  nat -> row -> Type :=
  bounded_obligation_replay.

(*
  (78)
  We record that every large enough seed-window realization builds a bounded obligation replay.
*)

Definition audit_local_seed_window_realization_builds_bounded_obligation_replay :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_obligation_replay N u :=
  local_seed_window_realization_builds_bounded_obligation_replay.

(*
  (79)
  We record that a bounded obligation replay forces a hot left coordinate.
*)

Definition audit_bounded_obligation_replay_forces_left_hot_coordinate :
  forall N u,
    audit_bounded_obligation_replay N u ->
    exists x,
      (- Z.of_nat (N + 3) <= x <= -3)%Z /\
      u x = true :=
  bounded_obligation_replay_forces_left_hot_coordinate.

(*
  (80)
  We record the seed-window corollary of that forced left coordinate.
*)

Definition audit_local_seed_window_realization_forces_left_hot_coordinate :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    exists x,
      (- Z.of_nat (N + 3) <= x <= -3)%Z /\
      u x = true :=
  local_seed_window_realization_forces_left_hot_coordinate.

(*
  (81)
  We define the bounded left-obligation chain.
*)

Definition audit_bounded_left_obligation_chain :
  nat -> row -> Type :=
  bounded_left_obligation_chain.

(*
  (82)
  We record that every seed-window realization builds such a chain.
*)

Definition audit_local_seed_window_realization_builds_bounded_left_obligation_chain :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_left_obligation_chain N u :=
  local_seed_window_realization_builds_bounded_left_obligation_chain.

(*
  (83)
  We record that each level of the chain forces a hot coordinate.
*)

Definition audit_bounded_left_obligation_chain_forces_coordinate_at_level :
  forall N u (C : audit_bounded_left_obligation_chain N u) k,
    (k <= N)%nat ->
    exists x,
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true :=
  bounded_left_obligation_chain_forces_coordinate_at_level.

(*
  (84)
  We record the seed-window version of the levelwise left-coordinate forcing.
*)

Definition audit_local_seed_window_realization_forces_left_hot_coordinate_at_each_level :
  forall N u k,
    (k <= N)%nat ->
    audit_local_seed_window_realization (S (S N)) u ->
    exists x,
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true :=
  local_seed_window_realization_forces_left_hot_coordinate_at_each_level.

(*
  (85)
  We define the bounded left-coordinate family.
*)

Definition audit_bounded_left_coordinate_family :
  nat -> row -> Type :=
  bounded_left_coordinate_family.

(*
  (86)
  We record that every seed-window realization builds a bounded left-coordinate family.
*)

Definition audit_local_seed_window_realization_builds_bounded_left_coordinate_family :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_left_coordinate_family N u :=
  local_seed_window_realization_builds_bounded_left_coordinate_family.

(*
  (87)
  We define the left cold slab predicate.
*)

Definition audit_left_cold_slab :
  nat -> row -> Prop :=
  left_cold_slab.

(*
  (88)
  We record that a bounded left-coordinate family forbids a cold left slab.
*)

Definition audit_bounded_left_coordinate_family_implies_left_slab_nonzero :
  forall N u,
    audit_bounded_left_coordinate_family N u ->
    ~ audit_left_cold_slab N u :=
  bounded_left_coordinate_family_implies_left_slab_nonzero.

(*
  (89)
  We record the direct seed-window impossibility of a cold left slab.
*)

Definition audit_local_seed_window_realization_left_cold_slab_impossible :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    ~ audit_left_cold_slab N u :=
  local_seed_window_realization_left_cold_slab_impossible.

(*
  (90)
  We define the packaged Phase 2 memory certificate.
*)

Definition audit_phase2_memory_certificate :
  nat -> row -> Type :=
  phase2_memory_certificate.

(*
  (91)
  We record the Phase 2 endpoint: every cutoff still remembers the seed.
*)

Definition audit_phase2_endpoint :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_phase2_memory_certificate N u :=
  every_cutoff_still_remembers_seed.

(*************************************************************************)
(*                                                                       *)
(*  Phase 2 Memory Theorem                                               *)
(*                                                                       *)
(*  Term.                                                                *)
(*                                                                       *)
(*    forall N u,                                                        *)
(*      local_seed_window_realization (S (S N)) u ->                     *)
(*      phase2_memory_certificate N u                                    *)
(*                                                                       *)
(*  Semantic reading.                                                    *)
(*                                                                       *)
(*    Every bounded cutoff still remembers the seed.  A local replay     *)
(*    of the centered seed cannot become semantically neutral: Rule 30   *)
(*    forces a bounded asymmetry certificate on the left slab.           *)
(*                                                                       *)
(*  Qualification.                                                       *)
(*                                                                       *)
(*    This endpoint is established fact inside T004.  The dependency     *)
(*    chain of every_cutoff_still_remembers_seed is closed under the     *)
(*    global context: no axioms and no admitted steps remain in this     *)
(*    Phase 2 package.                                                   *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                            PHASE THREE                                *)
(*                                                                       *)
(*************************************************************************)


(*
  (92)
  We define the finite glitchprojection object.
*)

Definition audit_glitchprojection (n k : nat) : Type :=
  glitchprojection n k.

(*
  (93)
  We define restriction of a glitchprojection to smaller width.
*)

Definition audit_glitchprojection_restrict_width :
  forall m n k,
    (m <= n)%nat ->
    audit_glitchprojection n k ->
    audit_glitchprojection m k :=
  glitchprojection_restrict_width.

(*
  (94)
  We define the profile predicate of a glitchprojection.
*)

Definition audit_glitchprojection_profile
    {n k : nat} (G : audit_glitchprojection n k) : Prop :=
  glitchprojection_profile G.

(*
  (95)
  We record classification of every glitchprojection profile.
*)

Definition audit_glitchprojection_profile_classification :
  forall n k (G : audit_glitchprojection n k),
    audit_glitchprojection_profile G :=
  glitchprojection_profile_classification.

(*
  (96)
  We record that left/right extra-side conditions force bilaterality at
  smaller width.
*)

Definition audit_glitchprojection_opposite_sides_force_bilateral_on_smaller_width :
  forall m n k (Hmn : (m <= n)%nat) (G : audit_glitchprojection n k),
    glitchprojection_extra_left G ->
    glitchprojection_extra_right
      (audit_glitchprojection_restrict_width m n k Hmn G) ->
    glitchprojection_bilateral
      (audit_glitchprojection_restrict_width m n k Hmn G) :=
  glitchprojection_opposite_sides_force_bilateral_on_smaller_width.

(*
  (97)
  We record impossibility of the compact Original Sin trap.
*)

Definition audit_compact_original_sin_trap_impossible :
  forall r c,
    compact_original_sin_trap r c ->
    False :=
  compact_original_sin_trap_impossible.

(*
  (98)
  Bounded periodic replay fragment used by the auxiliary compact-trap
  vocabulary.
*)

Definition audit_bounded_periodic_replay_fragment
    (n P H : nat) : Type :=
  bounded_periodic_replay_fragment n P H.

(*
  (99)
  We define the seed-forcing glitch predicate on a bounded replay fragment.
*)

Definition audit_seed_forcing_glitch
    (n P H : nat) (F : audit_bounded_periodic_replay_fragment n P H) :
    glitch_site -> Prop :=
  seed_forcing_glitch n P H F.

(*
  (100)
  We define the compact center trap on a bounded replay fragment.
*)

Definition audit_compact_center_trap_on_fragment
    (n P H : nat) (F : audit_bounded_periodic_replay_fragment n P H)
    (g : glitch_site) : Prop :=
  compact_center_trap_on_fragment n P H F g.

(*  The hidden-support descent route is omitted from the live package    *)
(*  surface.  The remaining Phase 3 development begins with eventual     *)
(*  periodicity and its semantic reformulations.                         *)

(*
  (104)
  We define eventual periodicity of the centered window.
*)

Definition audit_eventually_periodic_center_window :
  nat -> Prop :=
  eventually_periodic_center_window.

(*
  (105)
  We define observational periodicity from a specific cutoff and period.
*)

Definition audit_observational_periodic_tail_from :
  nat -> nat -> nat -> Prop :=
  observational_periodic_tail_from.

(*
  (106)
  We define the BHK-style upgrade principle from observation to uniformity.
*)

Definition audit_bhk_window_upgrade_principle : Prop :=
  bhk_window_upgrade_principle.

(*
  (107)
  We define the one-step semantic faithfulness principle of outward window growth.
*)

Definition audit_faithful_window_growth_principle : Prop :=
  faithful_window_growth_principle.

(*
  (108)
  We define a faithful observational periodic-tail realizer.
*)

Definition audit_faithful_observational_periodic_tail_realizer :
  nat -> Type :=
  faithful_observational_periodic_tail_realizer.

(*
  (109)
  We define realizable observational periodic tails at fixed width.
*)

Definition audit_realizable_observational_periodic_tail_from :
  nat -> Prop :=
  realizable_observational_periodic_tail_from.

(*
  (110)
  We define uniform eventual periodicity across all larger widths.
*)

Definition audit_uniformly_eventually_periodic_from :
  nat -> nat -> nat -> Prop :=
  uniformly_eventually_periodic_from.

(*
  (111)
  We define realizable uniform periodic tails.
*)

Definition audit_realizable_uniform_periodic_tail_from :
  nat -> Prop :=
  realizable_uniform_periodic_tail_from.

(*
  (112)
  We define eventual periodicity of full rows from a cutoff.
*)

Definition audit_eventually_periodic_full_rows_from :
  nat -> nat -> Prop :=
  eventually_periodic_full_rows_from.

(*
  (113)
  We define a finite periodic orbit block.
*)

Definition audit_finite_periodic_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  finite_periodic_orbit.

(*
  (114)
  We define a finite repeat block.
*)

Definition audit_finite_repeat_block :
  nat -> nat -> nat -> nat -> Prop :=
  finite_repeat_block.

(*
  (115)
  We define the centered finite window of an arbitrary row.
*)

Definition audit_row_window :
  row -> nat -> list bit :=
  row_window.

(*
  (116)
  We define local realization of a target window by a predecessor row.
*)

Definition audit_local_target_window_realization :
  nat -> row -> row -> Prop :=
  local_target_window_realization.

(*
  (117)
  We define the predecessor carrier window at one larger radius.
*)

Definition audit_predecessor_carrier_window :
  nat -> row -> list bit :=
  predecessor_carrier_window.

(*
  (118)
  We define the length of a predecessor carrier window.
*)

Definition audit_predecessor_carrier_length :
  nat -> nat :=
  predecessor_carrier_length.

(*
  (119)
  We define the finite Rule 30 window operator on carriers.
*)

Definition audit_rule30_window :
  list bit -> list bit :=
  rule30_window.

(*
  (120)
  We define recovery of the missing left bit from the Rule 30 output.
*)

Definition audit_recover_left_bit :
  bit -> bit -> bit -> bit :=
  recover_left_bit.

(*
  (121)
  We define the cutoff predecessor row indexed along a periodic orbit.
*)

Definition audit_cutoff_predecessor :
  nat -> nat -> nat -> row :=
  cutoff_predecessor.

(*
  (122)
  We define the predecessor carrier of a cutoff predecessor row.
*)

Definition audit_cutoff_predecessor_carrier :
  nat -> nat -> nat -> nat -> list bit :=
  cutoff_predecessor_carrier.

(*
  (123)
  We define the reversed Rule 30 window operator.
*)

Definition audit_rule30_window_rev :
  list bit -> list bit :=
  rule30_window_rev.

(*
  (124)
  We define reverse reconstruction of a carrier from boundary data.
*)

Definition audit_reconstruct_carrier_rev :
  list bit -> bit -> bit -> list bit :=
  reconstruct_carrier_rev.

(*
  (125)
  We define when a carrier realizes a target window.
*)

Definition audit_carrier_realizes_window :
  nat -> list bit -> list bit -> Prop :=
  carrier_realizes_window.

(*
  (126)
  We define the canonical cutoff window at phase T.
*)

Definition audit_canonical_cutoff_window :
  nat -> nat -> list bit :=
  canonical_cutoff_window.

(*
  (127)
  We define the finite carrier-memory orbit attached to a periodic block.
*)

Definition audit_finite_carrier_memory_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  finite_carrier_memory_orbit.

(*
  (128)
  We define the one-step backward transport carrier orbit.
*)

Definition audit_backward_transport_carrier_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  backward_transport_carrier_orbit.

(*
  (129)
  We define repeated predecessor carriers inside a finite orbit.
*)

Definition audit_repeated_cutoff_predecessor_carrier :
  nat -> nat -> nat -> nat -> Prop :=
  repeated_cutoff_predecessor_carrier.

(*
  (130)
  We define the finite carrier pool at a given radius.
*)

Definition audit_carrier_pool :
  nat -> list (list bit) :=
  carrier_pool.

(*
  (131)
  We record the size of the finite carrier pool.
*)

Definition audit_carrier_pool_length :
  forall R,
    length (audit_carrier_pool R) =
    Nat.pow 2 (audit_predecessor_carrier_length R) :=
  carrier_pool_length.

(*
  (132)
  We record the fixed length of every predecessor carrier window.
*)

Definition audit_predecessor_carrier_window_length :
  forall R u,
    length (audit_predecessor_carrier_window R u) =
    audit_predecessor_carrier_length R :=
  predecessor_carrier_window_length.

(*
  (133)
  We record that the recovered left bit reproduces the given Rule 30 output.
*)

Definition audit_rule30_recovers_left_bit :
  forall o b c,
    rule30 (audit_recover_left_bit o b c) b c = o :=
  rule30_recovers_left_bit.

(*
  (134)
  We record uniqueness of that recovered left bit.
*)

Definition audit_recover_left_bit_unique :
  forall a o b c,
    rule30 a b c = o ->
    a = audit_recover_left_bit o b c :=
  recover_left_bit_unique.

(*
  (135)
  We record the length of reverse carrier reconstruction.
*)

Definition audit_reconstruct_carrier_rev_from_length :
  forall outs_rev b c,
    length (reconstruct_carrier_rev_from outs_rev b c) =
    S (S (length outs_rev)) :=
  reconstruct_carrier_rev_from_length.

(*
  (136)
  We record that reverse reconstruction reproduces the prescribed outputs.
*)

Definition audit_rule30_window_rev_reconstructs_outputs :
  forall outs_rev b c,
    audit_rule30_window_rev (reconstruct_carrier_rev_from outs_rev b c) =
    outs_rev :=
  rule30_window_rev_reconstructs_outputs.

(*
  (137)
  We record boundary-based determination of the reverse carrier.
*)

Definition audit_rule30_window_rev_determined_by_boundary :
  forall outs_rev b c rest,
    audit_rule30_window_rev (c :: b :: rest) = outs_rev ->
    c :: b :: rest = reconstruct_carrier_rev_from outs_rev b c :=
  rule30_window_rev_determined_by_boundary.

(*
  (138)
  We define the two-bit right-boundary signature of a carrier.
*)

Definition audit_carrier_right_boundary_signature :
  list bit -> bit * bit :=
  carrier_right_boundary_signature.

(*
  (139)
  We record additivity of iterated row evolution.
*)

Definition audit_iter_row_plus :
  forall a b r,
    iter_row (a + b) r = iter_row a (iter_row b r) :=
  iter_row_plus.

(*
  (140)
  We record the canonical row as a shifted iterate of the automaton.
*)

Definition audit_canonical_row_after :
  forall t s,
    canonical_row (t + s)%nat = iter_row s (canonical_row t) :=
  canonical_row_after.

(*
  (141)
  We record Rule 30 evaluation on a centered predecessor carrier.
*)

Definition audit_rule30_window_on_centered_carrier :
  forall R u,
    audit_rule30_window (audit_predecessor_carrier_window R u) =
    audit_row_window (step u) R :=
  rule30_window_on_centered_carrier.

(*
  (142)
  We record weakening of centered-window equality to smaller radius.
*)

Definition audit_center_window_eq_weaken :
  forall n m t u,
    (m <= n)%nat ->
    center_window n t = center_window n u ->
    center_window m t = center_window m u :=
  center_window_eq_weaken.

(*
  (143)
  We record forward transport of a repeated larger window.
*)

Definition audit_center_window_repeat_transports_forward :
  forall radius steps a b,
    center_window (radius + steps) a = center_window (radius + steps) b ->
    center_window radius (a + steps)%nat =
    center_window radius (b + steps)%nat :=
  center_window_repeat_transports_forward.

(*
  (144)
  We record blockwise forward transport of repeated larger windows.
*)

Definition audit_center_window_repeat_transports_forward_block :
  forall radius extra a b s,
    (s <= extra)%nat ->
    center_window (radius + extra) a = center_window (radius + extra) b ->
    center_window radius (a + s)%nat =
    center_window radius (b + s)%nat :=
  center_window_repeat_transports_forward_block.

(*
  (145)
  We record that eventual periodicity freezes the cutoff phase.
*)

Definition audit_eventual_periodicity_freezes_cutoff_phase :
  forall n T P,
    (0 < P)%nat ->
    (forall t,
      center_window n (T + t + P)%nat =
      center_window n (T + t)%nat) ->
    forall m,
        center_window n (T + m * P)%nat = center_window n T :=
  eventual_periodicity_freezes_cutoff_phase.

(*
  (146)
  We record that cutoff predecessors realize the fixed cutoff target window.
*)

Definition audit_cutoff_predecessor_realizes_cutoff_target_window :
  forall n T P m,
    (0 < P)%nat ->
    (forall t,
      center_window n (T + t + P)%nat =
      center_window n (T + t)%nat) ->
    audit_local_target_window_realization n (canonical_row T)
      (audit_cutoff_predecessor T P m) :=
  cutoff_predecessor_realizes_cutoff_target_window.

(*
  (147)
  We record the repeated local predecessor formulation of eventual periodicity.
*)

Definition audit_eventual_periodicity_yields_repeated_cutoff_predecessors :
  forall n,
    audit_eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        audit_local_target_window_realization n (canonical_row T)
          (audit_cutoff_predecessor T P m) :=
  eventual_periodicity_yields_repeated_cutoff_predecessors.

(*
  (148)
  We record tail trimming for a finite periodic orbit block.
*)

Definition audit_finite_periodic_orbit_tail_trim :
  forall n T P K,
    audit_finite_periodic_orbit n T P (S K) ->
    audit_finite_periodic_orbit n T P K :=
  finite_periodic_orbit_tail_trim.

(*
  (149)
  We record the successor-step equality inside a finite periodic orbit.
*)

Definition audit_finite_periodic_orbit_successor_step :
  forall n T P K m,
    audit_finite_periodic_orbit n T P (S K) ->
    (m <= K)%nat ->
    center_window n (T + (S m) * P)%nat = center_window n T :=
  finite_periodic_orbit_successor_step.

(*
  (150)
  We record that eventual periodicity yields finite periodic orbit blocks of every length.
*)

Definition audit_eventual_periodicity_implies_finite_periodic_orbit :
  forall n,
    audit_eventually_periodic_center_window n ->
    forall K,
      exists T P,
        audit_finite_periodic_orbit n T P K :=
  eventual_periodicity_implies_finite_periodic_orbit.

(*
  (151)
  We record the finite-orbit version of cutoff-predecessor realization.
*)

Definition audit_cutoff_predecessor_realizes_cutoff_target_window_from_finite_orbit :
  forall n T P K m,
    audit_finite_periodic_orbit n T P (S K) ->
    (m <= K)%nat ->
    audit_local_target_window_realization n (canonical_row T)
      (audit_cutoff_predecessor T P m) :=
  cutoff_predecessor_realizes_cutoff_target_window_from_finite_orbit.

(*
  (152)
  We record the cutoff predecessor carrier orbit extracted from eventual periodicity.
*)

Definition audit_eventual_periodicity_yields_cutoff_predecessor_carrier_orbit :
  forall n,
    audit_eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        audit_local_target_window_realization n (canonical_row T)
          (audit_cutoff_predecessor T P m) /\
        length (audit_cutoff_predecessor_carrier n T P m) =
          audit_predecessor_carrier_length n :=
  eventual_periodicity_yields_cutoff_predecessor_carrier_orbit.

(*
  (153)
  We record that each cutoff predecessor carrier realizes the fixed cutoff window.
*)

Definition audit_cutoff_predecessor_carrier_realizes_cutoff_window :
  forall R T P m,
    (0 < P)%nat ->
    (forall t,
      center_window R (T + t + P)%nat =
      center_window R (T + t)%nat) ->
    audit_carrier_realizes_window R
      (audit_canonical_cutoff_window R T)
      (audit_cutoff_predecessor_carrier R T P m) :=
  cutoff_predecessor_carrier_realizes_cutoff_window.

(*
  (154)
  We record the finite carrier-memory orbit extracted from eventual periodicity.
*)

Definition audit_eventual_periodicity_yields_carrier_memory_orbit :
  forall n,
    audit_eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        audit_carrier_realizes_window n
          (audit_canonical_cutoff_window n T)
          (audit_cutoff_predecessor_carrier n T P m) :=
  eventual_periodicity_yields_carrier_memory_orbit.

(*
  (155)
  We record that finite periodic orbits induce finite carrier-memory orbits.
*)

Definition audit_finite_periodic_orbit_implies_finite_carrier_memory_orbit :
  forall n T P K,
    audit_finite_periodic_orbit n T P (S K) ->
    audit_finite_carrier_memory_orbit n T P K :=
  finite_periodic_orbit_implies_finite_carrier_memory_orbit.

(*
  (156)
  We record one-step backward transport from a finite periodic orbit.
*)

Definition audit_finite_periodic_orbit_transports_backward_one_step :
  forall n T P K,
    audit_finite_periodic_orbit n (S T) P (S K) ->
    audit_backward_transport_carrier_orbit n T P K :=
  finite_periodic_orbit_transports_backward_one_step.

(*
  (157)
  We record that equal predecessor carriers at the successor cutoff transport backward.
*)

Definition audit_equal_cutoff_predecessor_carriers_at_successor_cutoff_transport_backward :
  forall R T P i j,
    (0 < P)%nat ->
    audit_cutoff_predecessor_carrier R (S T) P i =
    audit_cutoff_predecessor_carrier R (S T) P j ->
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  equal_cutoff_predecessor_carriers_at_successor_cutoff_transport_backward.

(*
  (158)
  We record the repeated-carrier version of that backward transport.
*)

Definition audit_repeated_cutoff_predecessor_carrier_at_successor_cutoff_transports_backward :
  forall R T P K,
    (0 < P)%nat ->
    audit_repeated_cutoff_predecessor_carrier R (S T) P K ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  repeated_cutoff_predecessor_carrier_at_successor_cutoff_transports_backward.

(*
  (159)
  We record backward transport from finite periodicity plus a repeated carrier.
*)

Definition audit_finite_periodic_orbit_plus_repeated_carrier_transports_backward :
  forall R T P K,
    audit_finite_periodic_orbit R (S T) P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R (S T) P K ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  finite_periodic_orbit_plus_repeated_carrier_transports_backward.

(*
  (160)
  We record the pigeonhole step on long finite carrier-memory orbits.
*)

Definition audit_long_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (length (audit_carrier_pool R) < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  long_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (161)
  We record the repeated-carrier corollary for long finite periodic orbits.
*)

Definition audit_long_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (length (audit_carrier_pool R) < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  long_finite_periodic_orbit_has_repeated_carrier.

(*
  (162)
  We record backward transport from sufficiently long finite periodic orbits.
*)

Definition audit_long_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (length (audit_carrier_pool R) < S K)%nat ->
    audit_finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  long_finite_periodic_orbit_transports_backward.

(*
  (163)
  We record the exponential-size pigeonhole bound on finite carrier-memory orbits.
*)

Definition audit_large_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (audit_predecessor_carrier_length R) < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  large_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (164)
  We record the exponential-size repeated-carrier corollary for finite periodic orbits.
*)

Definition audit_large_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (audit_predecessor_carrier_length R) < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  large_finite_periodic_orbit_has_repeated_carrier.

(*
  (165)
  We record exponential-size backward transport for finite periodic orbits.
*)

Definition audit_large_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (Nat.pow 2 (audit_predecessor_carrier_length R) < S K)%nat ->
    audit_finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  large_finite_periodic_orbit_transports_backward.

(*
  (166)
  We record a first backward-repeat theorem for a periodic tail at the successor cutoff.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_backward_repeat :
  forall R T P,
    (0 < P)%nat ->
    (forall t,
      center_window R (S T + t + P)%nat =
      center_window R (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= Nat.pow 2 (audit_predecessor_carrier_length R))%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  periodic_tail_at_successor_cutoff_has_backward_repeat.

(*
  (167)
  We record the blockwise version of that backward-repeat theorem.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_backward_repeat_block :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= Nat.pow 2 (audit_predecessor_carrier_length (R + extra)))%nat /\
      forall s,
        (s <= extra)%nat ->
        center_window (S R) (T + (S i) * P + s)%nat =
        center_window (S R) (T + (S j) * P + s)%nat :=
  periodic_tail_at_successor_cutoff_has_backward_repeat_block.

(*
  (168)
  We record that the predecessor carrier determines the target window.
*)

Definition audit_predecessor_carrier_window_determines_target_window :
  forall R u v,
    audit_predecessor_carrier_window R u =
    audit_predecessor_carrier_window R v ->
    audit_row_window (step u) R = audit_row_window (step v) R :=
  predecessor_carrier_window_determines_target_window.

(*
  (169)
  We record the exact equivalence between local target realization and Rule 30 carrier evaluation.
*)

Definition audit_local_target_window_realization_iff_rule30_window :
  forall R target u,
    audit_local_target_window_realization R target u <->
    audit_rule30_window (audit_predecessor_carrier_window R u) =
    audit_row_window target R :=
  local_target_window_realization_iff_rule30_window.

(*
  (170)
  We record that local target realization respects equality of predecessor carriers.
*)

Definition audit_local_target_window_realization_respects_predecessor_carrier :
  forall R target u v,
    audit_predecessor_carrier_window R u =
    audit_predecessor_carrier_window R v ->
    audit_local_target_window_realization R target u ->
    audit_local_target_window_realization R target v :=
  local_target_window_realization_respects_predecessor_carrier.

(*
  (171)
  We record boundary-signature determination of local target realization.
*)

Definition audit_local_target_window_realization_determined_by_boundary_signature :
  forall R target u v,
    audit_local_target_window_realization R target u ->
    audit_local_target_window_realization R target v ->
    audit_carrier_right_boundary_signature
      (audit_predecessor_carrier_window R u) =
    audit_carrier_right_boundary_signature
      (audit_predecessor_carrier_window R v) ->
    audit_predecessor_carrier_window R u =
    audit_predecessor_carrier_window R v :=
  local_target_window_realization_determined_by_boundary_signature.

(*
  (172)
  We record the four-state pigeonhole step on finite carrier-memory orbits.
*)

Definition audit_small_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  small_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (173)
  We record the four-state repeated-carrier corollary for finite periodic orbits.
*)

Definition audit_small_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  small_finite_periodic_orbit_has_repeated_carrier.

(*
  (174)
  We record the four-state backward transport theorem for finite periodic orbits.
*)

Definition audit_small_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (4 < S K)%nat ->
    audit_finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  small_finite_periodic_orbit_transports_backward.

(*
  (175)
  We record the sharpened small backward-repeat theorem for periodic tails.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_small_backward_repeat :
  forall R T P,
    (0 < P)%nat ->
    (forall t,
      center_window R (S T + t + P)%nat =
      center_window R (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= 4)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat :=
  periodic_tail_at_successor_cutoff_has_small_backward_repeat.

(*
  (176)
  We record the blockwise sharpened small backward-repeat theorem.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_small_backward_repeat_block :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= 4)%nat /\
      forall s,
        (s <= extra)%nat ->
        center_window (S R) (T + (S i) * P + s)%nat =
        center_window (S R) (T + (S j) * P + s)%nat :=
  periodic_tail_at_successor_cutoff_has_small_backward_repeat_block.

(*
  (177)
  We record conversion of a small backward-repeat block into a finite repeat block.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_small_backward_finite_repeat_block :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists T' P',
      (T + P <= T')%nat /\
      (T' <= T + 4 * P)%nat /\
      (P' <= 4 * P)%nat /\
      audit_finite_repeat_block (S R) T' P' extra :=
  periodic_tail_at_successor_cutoff_has_small_backward_finite_repeat_block.

(*
  (178)
  We record extraction of an unbounded small backward pair from a uniform periodic tail.
*)

Definition audit_periodic_tail_at_successor_cutoff_has_unbounded_small_backward_pair :
  forall R T P,
    (0 < P)%nat ->
    (forall extra t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists i j,
      In (i, j) small_backward_pair_pool /\
      forall N,
        exists extra,
          (N <= extra)%nat /\
          small_backward_pair_block R T P extra (i, j) :=
  periodic_tail_at_successor_cutoff_has_unbounded_small_backward_pair.

(*
  (179)
  We record transport of a uniform periodic tail to bounded eventual periodicity at larger radius.
*)

Definition audit_periodic_tail_at_successor_cutoff_transports_to_bounded_eventual_periodicity :
  forall R T P,
    (0 < P)%nat ->
    (forall extra t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists T' P',
      (T + P <= T')%nat /\
      (T' <= T + 4 * P)%nat /\
      (0 < P' <= 4 * P)%nat /\
      forall t,
        center_window (S R) (T' + t + P')%nat =
        center_window (S R) (T' + t)%nat :=
  periodic_tail_at_successor_cutoff_transports_to_bounded_eventual_periodicity.

(*
  (180)
  We record one-step transport of uniform eventual periodicity to larger radius.
*)

Definition audit_uniformly_eventually_periodic_from_transports_to_larger_radius :
  forall R T P,
    audit_uniformly_eventually_periodic_from R (S T) P ->
    exists T' P',
      (T + P <= T')%nat /\
      (T' <= T + 4 * P)%nat /\
      (0 < P' <= 4 * P)%nat /\
      audit_uniformly_eventually_periodic_from (S R) T' P' :=
  uniformly_eventually_periodic_from_transports_to_larger_radius.

(*
  (181)
  We record the positive-cutoff version of that one-step transport theorem.
*)

Definition audit_positive_uniformly_eventually_periodic_from_transports_to_larger_radius :
  forall R T P,
    (0 < T)%nat ->
    audit_uniformly_eventually_periodic_from R T P ->
    exists T' P',
      (0 < T')%nat /\
      audit_uniformly_eventually_periodic_from (S R) T' P' :=
  positive_uniformly_eventually_periodic_from_transports_to_larger_radius.

(*
  (182)
  We record iteration of positive-cutoff uniform transport to arbitrary larger radius.
*)

Definition audit_positive_uniformly_eventually_periodic_from_iterates :
  forall steps R T P,
    (0 < T)%nat ->
    audit_uniformly_eventually_periodic_from R T P ->
    exists T' P',
      (0 < T')%nat /\
      audit_uniformly_eventually_periodic_from (R + steps) T' P' :=
  positive_uniformly_eventually_periodic_from_iterates.

(*
  (183)
  We record that uniform window periodicity implies full-row eventual periodicity.
*)

Definition audit_uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity :
  forall R T P,
    audit_uniformly_eventually_periodic_from R T P ->
    audit_eventually_periodic_full_rows_from T P :=
  uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity.

(*
  (184)
  We record impossibility of eventual periodicity for full canonical rows.
*)

Definition audit_eventually_periodic_full_rows_from_impossible :
  forall T P,
    audit_eventually_periodic_full_rows_from T P ->
    False :=
  eventually_periodic_full_rows_from_impossible.

(*
  (185)
  Fixed-radius uniform eventual periodicity is impossible.

  Under a BHK reading, a periodicity claim is semantically significant only
  when it is given by a closed, uniform, terminating witness.  The theorem
  below denies exactly such a witness for a periodic tail.  It therefore
  does not deny that long finite stretches of repeating signatures may be
  observed empirically; rather, it says that no such finite evidence can be
  promoted to certainty that the repetition is final rather than transient.
*)

Definition audit_uniformly_eventually_periodic_from_impossible :
  forall R T P,
    audit_uniformly_eventually_periodic_from R T P ->
    False :=
  uniformly_eventually_periodic_from_impossible.

(*************************************************************************)
(*                                                                       *)
(*  No mixed center periodicity witness                                  *)
(*                                                                       *)
(*  Term.                                                                *)
(*                                                                       *)
(*    forall R T P,                                                      *)
(*      uniformly_eventually_periodic_from R T P -> False                *)
(*                                                                       *)
(*  Semantic reading.                                                    *)
(*                                                                       *)
(*    No faithful, closed, uniform periodic tail exists for the seeded   *)
(*    Rule 30 center.  Long finite or quasi-periodic behavior may be     *)
(*    observed empirically, but it cannot be promoted to a genuine       *)
(*    infinite periodic tail by a uniform terminating witness.           *)
(*                                                                       *)
(*  Qualification.                                                       *)
(*                                                                       *)
(*    This is the strong semantic endpoint proved in R06.                *)
(*    It is the recommended semantic interface for the package.  It      *)
(*    does not use replay_compactness_principle.  The unresolved         *)
(*    conceptual step is the bridge from bare fixed-width observational  *)
(*    periodicity to this stronger uniform semantic notion.              *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                             PHASE FOUR                                *)
(*                                                                       *)
(*************************************************************************)

(*
  (186)
  Local realizability-theoretic form of aperiodicity.

  This is the radius-indexed version of the semantic endpoint.  For each
  observation width R, the realizability predicate for a faithful uniform
  periodic tail is empty.  The subsequent items are not cosmetic restatements
  but changes of logical form: they pass from the pointwise statement to
  canonical endpoint naming, global existential negation, observational
  counterparts, and finally the external bridge from semantic faithfulness to
  eventual aperiodicity.
*)

Definition audit_realizable_uniform_periodic_tail_from_impossible :
  forall R,
    ~ audit_realizable_uniform_periodic_tail_from R :=
  realizable_uniform_periodic_tail_from_impossible.

(*
  (186a)
  Canonical audit alias for the preferred semantic endpoint.
*)

Definition audit_phase3_semantic_endpoint :
  forall R,
    ~ audit_realizable_uniform_periodic_tail_from R :=
  realizable_uniform_periodic_tail_from_impossible.

(*
  (187)
  Existentially closed form of the same impossibility statement.

  Instead of fixing a radius first, this version says that there is no tuple
  of parameters witnessing any realizable uniform periodic tail at all.
*)

Definition audit_realizable_uniform_periodic_tail_impossible :
  ~ exists R T P, audit_uniformly_eventually_periodic_from R T P :=
  realizable_uniform_periodic_tail_impossible.

(*
  (188)
  The faithful observational interface is already inconsistent.

  At this level the tail is phrased observationally, but the witness is
  required to satisfy the semantic discipline encoded by faithful realization.
*)

Definition audit_faithful_observational_periodic_tail_realizer_impossible :
  forall R,
    audit_faithful_observational_periodic_tail_realizer R ->
    False :=
  faithful_observational_periodic_tail_realizer_impossible.

(*
  (189)
  Observational realizability is therefore empty as well.

  This is the modal/existential counterpart of the previous item: once the
  faithful realizer type has been ruled out, the associated realizability
  predicate has no inhabitants.
*)

Definition audit_realizable_observational_periodic_tail_from_impossible :
  forall R,
    ~ audit_realizable_observational_periodic_tail_from R :=
  realizable_observational_periodic_tail_from_impossible.

(*
  (190)
  Faithful outward growth may be iterated across finitely many radius steps.

  This is the transport mechanism that carries a local observational witness
  to larger finite windows while preserving the same semantic claim.
*)

Definition audit_faithful_window_growth_iterates :
  audit_faithful_window_growth_principle ->
  forall steps R T P,
    audit_observational_periodic_tail_from R T P ->
    audit_observational_periodic_tail_from (R + steps) T P :=
  faithful_window_growth_iterates.

(*
  (191)
  Faithful window growth induces the BHK upgrade principle.

  In proof-theoretic terms, the growth law is the semantic engine that turns
  width-local observation into the stronger uniform notion used by the main
  impossibility theorem.
*)

Definition audit_faithful_window_growth_implies_bhk_window_upgrade :
  audit_faithful_window_growth_principle ->
  audit_bhk_window_upgrade_principle :=
  faithful_window_growth_implies_bhk_window_upgrade.

(*
  (192)
  Once the BHK upgrade is available, observational periodic tails collapse.

  The point here is that observational periodicity is not ruled out directly;
  it is ruled out after being shown to entail the stronger uniform object that
  Phase Four has already excluded.
*)

Definition audit_observational_periodic_tail_from_impossible_under_bhk_upgrade :
  audit_bhk_window_upgrade_principle ->
  forall R T P,
    audit_observational_periodic_tail_from R T P ->
    False :=
  observational_periodic_tail_from_impossible_under_bhk_upgrade.

(*
  (193)
  Corresponding exclusion of eventual periodic center windows.

  This is the fixed-radius corollary obtained by packaging the previous tail
  statement into the standard eventual-periodicity predicate.
*)

Definition audit_eventually_periodic_center_window_impossible_under_bhk_upgrade :
  audit_bhk_window_upgrade_principle ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  eventually_periodic_center_window_impossible_under_bhk_upgrade.

(*
  (194)
  External premise isolating the semantic bridge.

  Rather than burying this assumption inside the proof spine, the development
  names it explicitly and lets the later corollaries depend on it transparently.
*)

Definition audit_classical_semantic_faithfulness : Prop :=
  classical_semantic_faithfulness.

(*
  (195)
  Under the external premise, the BHK upgrade principle follows.
*)

Definition audit_classical_semantic_faithfulness_implies_bhk_upgrade :
  audit_classical_semantic_faithfulness ->
  audit_bhk_window_upgrade_principle :=
  classical_semantic_faithfulness_implies_bhk_upgrade.

(*
  (196)
  External classical corollary at the observational-tail level.
*)

Definition audit_classical_semantics_excludes_observational_periodic_tails :
  audit_classical_semantic_faithfulness ->
  forall R T P,
    ~ audit_observational_periodic_tail_from R T P :=
  classical_semantics_excludes_observational_periodic_tails.

(*
  (197)
  External classical corollary at the eventual-periodicity level.
*)

Definition audit_classical_semantics_excludes_eventual_periodic_windows :
  audit_classical_semantic_faithfulness ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_eventual_periodic_windows.

(*
  (197a)
  Canonical audit alias for the preferred external corollary.
*)

Definition audit_phase3_external_corollary :
  audit_classical_semantic_faithfulness ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_eventual_periodic_windows.

(*
  (198)
  Global classical exclusion of eventual periodic center windows.

  This is the existential closure of the preceding fixed-radius statement.
*)

Definition audit_classical_semantics_excludes_any_eventual_periodic_window :
  audit_classical_semantic_faithfulness ->
  ~ exists R, audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_any_eventual_periodic_window.

(*************************************************************************)
(*                                                                       *)
(*  Rule 30 center is not eventually periodic                            *)
(*                                                                       *)
(*  Term.                                                                *)
(*                                                                       *)
(*    classical_semantic_faithfulness ->                                 *)
(*      forall R, ~ eventually_periodic_center_window R                  *)
(*                                                                       *)
(*  Semantic reading.                                                    *)
(*                                                                       *)
(*    If one accepts the external semantic-faithfulness premise that a   *)
(*    genuine periodic tail must grow outward faithfully with the Rule   *)
(*    30 semantics, then eventual periodicity of any centered window is  *)
(*    excluded.                                                          *)
(*                                                                       *)
(*  Qualification.                                                       *)
(*                                                                       *)
(*    This lives deliberately in R07 as the recommended assumption-      *)
(*    isolating wrapper.  The premise classical_semantic_faithfulness is *)
(*    not proved internally in T004; it packages the semantic bridge     *)
(*    cleanly instead of hiding it inside the core proof spine.          *)
(*                                                                       *)
(*************************************************************************)

(*
  (199)
  Re-export of the faithful observational realizer impossibility.
*)

Definition audit_faithful_observational_realizers_already_impossible :
  forall R,
    ~ audit_realizable_observational_periodic_tail_from R :=
  faithful_observational_realizers_already_impossible.

(*
  (200)
  Re-export of the faithful uniform realizer impossibility.
*)

Definition audit_faithful_uniform_realizers_already_impossible :
  forall R,
    ~ audit_realizable_uniform_periodic_tail_from R :=
  faithful_uniform_realizers_already_impossible.

End Proof_Index.
