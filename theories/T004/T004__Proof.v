(* `T004_Proof.v` *)

From Coq Require Import List ZArith.
Import ListNotations.

From T004 Require Import
  R01__Phase_One
  R02__Phase_Two
  R03__Phase_Three
  R04__First_Corollary
  R05__Second_Corollary.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 -- Audit Layer                                   *)
(*                                                                       *)
(*  This file serves as the proof-theoretic synopsis of `T004`.  It      *)
(*  introduces no new mathematical content.  Rather, it reorganizes      *)
(*  the development's public objects, its replay/compactness interface,  *)
(*  its closed cutoff-memory certificate, its direct semantic endpoint,  *)
(*  its external faithful-semantics corollary, and its finite            *)
(*  observation-only provenance corollary in one place.                  *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  Overview
  --------

  `T004` has one main constructive framework and two corollaries. The first
  three files `R01`-`R03` are the constructive spine of the package. `R04`
  and `R05` are corollary layers built on top of that framework rather than
  additional proof phases inside it.


    (i) Main Constructive Framework: Phase 1

        (a) Seed orbit, the Fall / No Progenitor Theorem, and the local
            obstruction layer.

        (b) Replay / admissibility / compactness route culminating in
            `no_pure_periodicity_of_centered_windows`.

    (ii) Main Constructive Framework: Phase 2

        (a) Seed return and cutoff-memory analysis culminating in
            `original_sin_theorem`.

        (b) Auxiliary finite reverse-side vocabulary for compact traps,
            hidden support, and glitchprojection structure.

    (iii) Main Constructive Framework: Phase 3

        (a) Periodicity and semantic interfaces.

        (b) Carrier-window and backward-transport toolkit.

        (c) Phase 3 internal corollaries culminating in
            `eventually_periodic_center_window_impossible_under_bhk_upgrade`.

    (iv) 1st Corollary

        (a) `R04__First_Corollary` packages the external faithful-semantics
            bridge and yields
            `classical_semantics_excludes_eventual_periodic_windows`.

    (v) 2nd Corollary

        (a) `R05__Second_Corollary` packages finite provenance ambiguity:
            the shell-level manipulation question, the exact four-point reverse
            predecessor family above a visible canonical observation, and
            `no_observation_only_tamper_checker`.

        (b) Audit-level complexity plausibility consequence for the nth center
            bit under a standard local-semantic model.
*)

(*************************************************************************)
(*                                                                       *)
(*                             PHASE ONE                                 *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  MAIN CONSTRUCTIVE FRAMEWORK: PHASE ONE
*)

(*
  (a)
  SEEDED ORBIT AND LOCAL OBSTRUCTION
*)

(*
  (1)
  Canonical single-seed initial row i.e. true at the origin and false everywhere
  else.
*)

Definition audit_seed_row : row :=
  seed_row.

(*
  (2)
  Canonical Rule 30 trajectory generated from the seed by forward iteration.
*)

Definition audit_canonical_row : nat -> row :=
  canonical_row.

(*
  (3)
  Centered finite window cut from the canonical trajectory at a chosen radius
  and time.
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
  Pure periodicity predicate for the centered window, with repetition required
  from time 0 rather than merely after a cutoff.
*)

Definition audit_purely_periodic_center_window : nat -> Prop :=
  purely_periodic_center_window.

(*
  (6)
  Phase 2 seed-window realization predicate, re-exported early because it is
  formulated directly in the seed/local-step geometry fixed above and is used
  throughout the later cutoff-memory route.
*)

Definition audit_local_seed_window_realization : nat -> row -> Prop :=
  local_seed_window_realization.

(*
  (7)
  Progenitor relation between finitely supported predecessor rows and their
  one-step outputs.
*)

Definition audit_progenitor : row -> row -> Prop :=
  progenitor.

(*
  (8)
  The Fall / No Progenitor Theorem:
  the centered seed row admits no finitely supported progenitor.
*)

Definition audit_the_fall :
  ~ exists u, progenitor u seed_row :=
  the_fall.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    The Fall / No Progenitor Theorem                                   *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Assume a finitely supported progenitor `u` of the seed,    *)
(*            with support bound N.                                      *)
(*                                                                       *)
(*    Step 2. Use the boundary-propagation lemmas to force               *)
(*            `u(-1) = false` and `u(0) = false.`                        *)
(*                                                                       *)
(*    Step 3. Evaluate the step equation at `x = 0` to force             *)
(*            `u(1) = true`.                                             *)
(*                                                                       *)
(*    Step 4. Evaluate again at `x = 1`, where `seed_row 1 = false`,     *)
(*            to obtain a contradiction.                                 *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    `~ exists u, progenitor u seed_row`                                *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    There is no finitely supported row `u` whose one-step Rule 30 image*)
(*    is exactly the centered seed row. The single seeded defect cannot  *)
(*    be created in one forward step by a finitely supported             *)
(*    predecessor.                                                       *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This theorem is closed under the global context. It is the rigid   *)
(*    local obstruction used by both the compactness route and the       *)
(*    bounded cutoff-memory route. In Phase 1, every higher-level        *)
(*    contradiction is organized to collapse back to this point.         *)
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
  (b)
  REPLAY / ADMISSIBILITY / COMPACTNESS ROUTE
*)

(*
  (1)
  Window data extracted from an arbitrary spacetime tableau.
*)

Definition audit_window_data : space_time -> nat -> nat -> list bit :=
  window_data.

(*
  (2)
  Finite replay radius attached to each horizon; this is the bounded inspection
  width used by the compactness-facing replay problem.
*)

Definition audit_finite_replay_radius : nat -> nat -> nat :=
  finite_replay_radius.

(*
  (3)
  Finite replay problem used by the compactness route: periodic data together
  with bounded admissibility equations.
*)

Definition audit_finite_replay_problem : nat -> nat -> Prop :=
  finite_replay_problem.

(*
  (4)
  The bare local seed-window predecessor problem is always satisfiable, so
  one-step local agreement alone cannot yield the contradiction.
*)

Definition audit_local_seed_window_predecessor_is_always_satisfiable :
  forall R,
    local_seed_window_predecessor R :=
  local_seed_window_predecessor_is_always_satisfiable.

(*
  (5)
  Pure periodicity yields finite replay at every horizon, providing the bridge
  from observation to the compactness-facing finite object.
*)

Definition audit_purely_periodic_implies_finite_replay_problem :
  forall n horizon,
    audit_purely_periodic_center_window n ->
    audit_finite_replay_problem n horizon :=
  purely_periodic_implies_finite_replay_problem.

(*
  (6)
  Upward admissibility as the infinite replay object extracted from all bounded
  replay data under compactness.
*)

Definition audit_upward_admissible : nat -> Prop :=
  upward_admissible.

(*
  (7)
  Compactness premise turning all finite replay data into admissibility. This is
  the sole explicit Phase 1 openness on the proof spine.
*)

Definition audit_replay_compactness_principle : Prop :=
  replay_compactness_principle.

(*
  (8)
  Candidate rows sitting above the seed in an admissible replay. These are the
  objects that eventually become progenitors.
*)

Definition audit_candidate_above_seed : row -> Prop :=
  candidate_above_seed.

(*
  (9)
  Admissibility produces such a candidate row.
*)

Definition audit_upward_admissibility_implies_candidate_row :
  forall n,
    audit_upward_admissible n ->
    exists u, audit_candidate_above_seed u :=
  upward_admissibility_implies_candidate_row.

(*
  (10)
  Every candidate row steps exactly to the seed.
*)

Definition audit_candidate_row_respects_step :
  forall u,
    audit_candidate_above_seed u ->
    forall x,
      step u x = seed_row x :=
  candidate_row_respects_step.

(*
  (11)
  Every admissible candidate row has finite support.
*)

Definition audit_candidate_row_has_finite_support :
  forall u,
    audit_candidate_above_seed u ->
    finitely_supported u :=
  candidate_row_has_finite_support.

(*
  (12)
  Every admissible candidate row is a progenitor of the seed.
*)

Definition audit_candidate_row_is_progenitor :
  forall u,
    audit_candidate_above_seed u ->
    progenitor u seed_row :=
  candidate_row_is_progenitor.

(*
  (13)
  Admissibility forces the seed to have a progenitor.
*)

Definition audit_upward_admissibility_implies_seed_has_progenitor :
  forall n,
    audit_upward_admissible n ->
    exists u, progenitor u seed_row :=
  upward_admissibility_implies_seed_has_progenitor.

(*
  (14)
  Contradiction packaged with periodic observation and upward admissibility.
*)

Definition audit_observable_periodicity_plus_upward_admissibility_contradict :
  forall n,
    audit_purely_periodic_center_window n ->
    audit_upward_admissible n ->
    False :=
  observable_periodicity_plus_upward_admissibility_contradict.

(*
  (15)
  Under the compactness premise, the Fall and classical nonadmissibility
  yield a finite replay obstruction.
*)

Definition audit_the_fall_implies_finite_replay_obstruction :
  audit_replay_compactness_principle ->
  forall n,
    exists horizon, ~ audit_finite_replay_problem n horizon :=
  the_fall_implies_finite_replay_obstruction.

(*
  (16)
  Phase 1 compactness corollary: no centered window is purely periodic.
*)

Definition audit_no_pure_periodicity_of_centered_windows :
  audit_replay_compactness_principle ->
  forall n,
    ~ audit_purely_periodic_center_window n :=
  no_pure_periodicity_of_centered_windows.

(*
  (17)
  Width-zero instance of the same compactness corollary.
*)

Definition audit_center_strip_not_purely_periodic :
  audit_replay_compactness_principle ->
  ~ audit_purely_periodic_center_window 0%nat :=
  center_strip_not_purely_periodic.

(*
  (18)
  Canonical audit alias for the Phase 1 compactness corollary.
*)

Definition audit_phase1_endpoint :
  audit_replay_compactness_principle ->
  forall n,
    ~ audit_purely_periodic_center_window n :=
  no_pure_periodicity_of_centered_windows.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Absurdity of Pure Periodicity                                      *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Convert pure periodicity of the radius-n centered window   *)
(*            into a bounded replay problem at every finite horizon.     *)
(*                                                                       *)
(*    Step 2. Apply `replay_compactness_principle` to obtain upward      *)
(*            admissibility above the seed.                              *)
(*                                                                       *)
(*    Step 3. Turn upward admissibility into a candidate row, hence      *)
(*            into a finitely supported `progenitor` of the seed.        *)
(*                                                                       *)
(*    Step 4. Contradict the Fall / No Progenitor Theorem.               *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    `replay_compactness_principle ->`                                  *)
(*    `  forall n, ~ purely_periodic_center_window n`                    *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Under the compactness premise, every finite radius n has the       *)
(*    property that the centered width-(2n+1) window of the seeded       *)
(*    Rule 30 evolution fails to be purely periodic from time 0.  Any    *)
(*    such periodicity hypothesis would generate bounded replay data at  *)
(*    every horizon; compactness would then produce an admissible row    *)
(*    above the seed, i.e. a forbidden `progenitor`.                     *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is an explicit compactness-conditional corollary assembled    *)
(*    inside the Phase 1 package from bounded replay, the compactness    *)
(*    premise, and the Fall. It is therefore a genuine Phase 1           *)
(*    endpoint, but                                                      *)
(*    not yet the strongest semantic endpoint of the overall package.    *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                             PHASE TWO                                 *)
(*                                                                       *)
(*************************************************************************)

(*
  (ii)
  MAIN CONSTRUCTIVE FRAMEWORK: PHASE TWO
*)

(*
  (a)
  SEED RETURN AND CUTOFF MEMORY
*)

(*
  (1)
  Truncation of a row to the radius-N window.  This is the basic finite
  carrier used throughout the Phase 2 reverse-side analysis.
*)

Definition audit_truncate : nat -> row -> row :=
  truncate.

(*
  (2)
  Finite-height prefix predicate asserting that a spacetime tableau agrees
  with the canonical seeded run up to level h.
*)

Definition audit_seeded_prefix : nat -> space_time -> Prop :=
  seeded_prefix.

(*
  (3)
  Time-shifted canonical spacetime, used to express seed return after a lag.
*)

Definition audit_shifted_canonical_trajectory : nat -> space_time :=
  shifted_canonical_trajectory.

(*
  (4)
  Predicate saying that the canonical seeded prefix reappears after lag P.
*)

Definition audit_seeded_prefix_repeats_after : nat -> nat -> Prop :=
  seeded_prefix_repeats_after.

(*
  (5)
  Any such prefix repetition forces literal return to the seed at time P.
*)

Definition audit_seeded_prefix_repeats_after_implies_seed_return :
  forall h P,
    audit_seeded_prefix_repeats_after h P ->
    canonical_row P = seed_row :=
  seeded_prefix_repeats_after_implies_seed_return.

(*
  (6)
  Positive-lag seeded-prefix repetition is therefore impossible.
*)

Definition audit_seeded_prefix_repeats_after_positive_period_impossible :
  forall h P,
    (0 < P)%nat ->
    ~ audit_seeded_prefix_repeats_after h P :=
  seeded_prefix_repeats_after_positive_period_impossible.

(*
  (7)
  A radius-(S N) seed window cannot be realized inside support [-N, N];
  some outer-shell activity is forced.
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
  (8)
  Support-bound reformulation of the same cutoff impossibility.
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
  Outer-shell and shell-obligation interface.
*)

(*
  (9)
  Outer-shell sites.
*)

Definition audit_outer_shell_site : Type :=
  outer_shell_site.

(*
  (10)
  Outer-shell coordinates.
*)

Definition audit_outer_shell_coord : nat -> audit_outer_shell_site -> Z :=
  outer_shell_coord.

(*
  (11)
  Outer-shell nonemptiness.
*)

Definition audit_outer_shell_nonempty : nat -> row -> Prop :=
  outer_shell_nonempty.

(*
  (12)
  Outer-shell signature.
*)

Definition audit_outer_shell_signature : nat -> row -> list bit :=
  outer_shell_signature.

(*
  (13)
  Seed-window realization emits outer-shell support.
*)

Definition audit_local_seed_window_realization_requires_outer_shell :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    exists x,
      (Z.of_nat N < Z.abs x <= Z.of_nat (S (S N)))%Z /\
      truncate (S (S N)) u x = true :=
  local_seed_window_realization_requires_outer_shell.

(*
  (14)
  Nonempty-shell reformulation of the emission fact.
*)

Definition audit_local_seed_window_realization_requires_outer_shell_nonempty :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_outer_shell_nonempty N u :=
  local_seed_window_realization_requires_outer_shell_nonempty.

(*
  (15)
  The emitted shell signature is never all zero.
*)

Definition audit_local_seed_window_realization_requires_nonzero_shell_signature :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_outer_shell_signature N u <> [false; false; false; false] :=
  local_seed_window_realization_requires_nonzero_shell_signature.

(*
  (16)
  Finite obligation type carried by the outer shell.

  The three cases isolate whether the forced support sits on the left,
  on the right, or on both sides simultaneously.
*)

Definition audit_shell_obligation : Type :=
  shell_obligation.

(*
  (17)
  Realization predicate for the left shell obligation.

  This says that the bounded realization already exhibits a hot witness
  at one of the two distinguished left shell sites.
*)

Definition audit_realizes_left_shell_obligation :
  nat -> row -> Prop :=
  realizes_left_shell_obligation.

(*
  (18)
  Realization predicate for the right shell obligation.

  This is the right-hand analogue of the preceding left-shell theorem: one of the two designated
  right shell sites is already forced to be hot.
*)

Definition audit_realizes_right_shell_obligation :
  nat -> row -> Prop :=
  realizes_right_shell_obligation.

(*
  (19)
  Uniform realization predicate for any shell obligation.

  It dispatches by obligation type and packages the bilateral case as
  simultaneous realization of both the left and right obligations.
*)

Definition audit_realizes_shell_obligation :
  nat -> row -> audit_shell_obligation -> Prop :=
  realizes_shell_obligation.

(*
  (20)
  Far-left persistence marker.

  This is the strongest left-facing shell witness: the outermost left
  shell coordinate itself is forced to be hot.
*)

Definition audit_far_left_hot : nat -> row -> Prop :=
  far_left_hot.

(*
  (21)
  Inner-right compactification marker.

  Instead of living on the outer shell, this witness says the truncated
  row is already hot at the inner right boundary coordinate `+N`.
*)

Definition audit_inner_right_hot : nat -> row -> Prop :=
  inner_right_hot.

(*
  (22)
  Right boundary zero-output equation.

  This is the local Rule 30 equation saying that the truncated row must
  produce `0` at the right boundary site of the seeded window.
*)

Definition audit_right_edge_zero_equation : nat -> row -> Prop :=
  right_edge_zero_equation.

(*
  (23)
  Left boundary zero-output equation.

  This is the symmetric left-hand version of the preceding right-boundary equation, again enforced by
  the requirement that the seeded successor vanish there.
*)

Definition audit_left_edge_zero_equation : nat -> row -> Prop :=
  left_edge_zero_equation.

(*
  (24)
  Seed-window realization forces the right boundary equation.

  Because the bounded successor must match `seed_row` on that boundary,
  the right edge output is compelled to be zero.
*)

Definition audit_right_edge_zero_equation_from_seed_window :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_right_edge_zero_equation N u :=
  right_edge_zero_equation_from_seed_window.

(*
  (25)
  Seed-window realization forces the left boundary equation.

  This is the left-hand companion of the preceding right-boundary theorem: legal realization of the seed
  window automatically imposes the zero-output equation there as well.
*)

Definition audit_left_edge_zero_equation_from_seed_window :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_left_edge_zero_equation N u :=
  left_edge_zero_equation_from_seed_window.

(*
  (26)
  Audit-facing OR form of the right edge equation.
  The imported source theorem still uses `_xor_obligation` in its name.

  Semantically, the vanishing right boundary output rewrites as an
  inclusive-OR constraint relating the inner right bit to the two right
  shell bits.
*)

Definition audit_right_edge_zero_equation_unfolds_to_or_obligation :
  forall N u,
    audit_right_edge_zero_equation N u ->
    truncate (S (S N)) u (Z.of_nat N) =
      orb (outer_shell_value N u outer_right)
          (outer_shell_value N u outer_far_right) :=
  right_edge_zero_equation_unfolds_to_xor_obligation.

(*
  (27)
  Audit-facing OR form of the left edge equation.
  The imported source theorem still uses `_xor_obligation` in its name.

  Here the left boundary zero equation rewrites as an inclusive-OR
  relation that determines the far-left shell bit from the nearer left
  shell bit and the inner truncated coordinate `-N`.
*)

Definition audit_left_edge_zero_equation_unfolds_to_or_obligation :
  forall N u,
    audit_left_edge_zero_equation N u ->
    outer_shell_value N u outer_far_left =
      orb (outer_shell_value N u outer_left)
          (truncate (S (S N)) u (- Z.of_nat N)) :=
  left_edge_zero_equation_unfolds_to_xor_obligation.

(*
  (28)
  Every legal seed-window realization emits a shell obligation.

  The point is that nontrivial support cannot disappear completely:
  some forced witness must appear on either the left or right shell.
*)

Definition audit_local_seed_window_realization_emits_shell_obligation :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_realizes_shell_obligation N u obligation_left \/
    audit_realizes_shell_obligation N u obligation_right :=
  local_seed_window_realization_emits_shell_obligation.

(*
  (29)
  Left shell obligation plus the left edge equation yields far-left pressure.

  Any left-side witness is enough: once the boundary equation is unfolded,
  the near-left case collapses to the stronger far-left hotness predicate.
*)

Definition audit_left_shell_obligation_forces_far_left_hot :
  forall N u,
    audit_left_edge_zero_equation N u ->
    audit_realizes_left_shell_obligation N u ->
    audit_far_left_hot N u :=
  left_shell_obligation_forces_far_left_hot.

(*
  (30)
  Right shell obligation yields inward pressure on the right.

  Using the right edge equation, any right-shell witness is transported
  from the shell into the inner-right hotness predicate.
*)

Definition audit_right_shell_obligation_forces_inner_right_hot :
  forall N u,
    audit_right_edge_zero_equation N u ->
    audit_realizes_right_shell_obligation N u ->
    audit_inner_right_hot N u :=
  right_shell_obligation_forces_inner_right_hot.

(*
  (31)
  First shell dichotomy for a legal bounded realization.

  A seeded realization of width `S N` cannot stay neutral: it already
  forces either left persistence or a right-side inward witness.
*)

Definition audit_local_seed_window_realization_forces_far_left_or_inner_right :
  forall N u,
    audit_local_seed_window_realization (S N) u ->
    audit_far_left_hot N u \/ audit_inner_right_hot N u :=
  local_seed_window_realization_forces_far_left_or_inner_right.

(*
  (32)
  Inner-right pressure compactifies to a smaller right obligation.

  A hot inner-right boundary bit at radius `S N` becomes a genuine
  right-shell obligation one radius lower, at radius `N`.
*)

Definition audit_inner_right_hot_compactifies_to_smaller_right_obligation :
  forall N u,
    audit_inner_right_hot (S N) u ->
    audit_realizes_right_shell_obligation N u :=
  inner_right_hot_compactifies_to_smaller_right_obligation.

(*
  (33)
  First recursive compactification dichotomy.

  At radius `S (S N)`, a legal realization either preserves left pressure
  at the wider shell or pushes the right-side obligation one step inward.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_or_right_compactification :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_far_left_hot (S N) u \/ audit_realizes_right_shell_obligation N u :=
  local_seed_window_realization_forces_left_persistence_or_right_compactification.

(*
  (34)
  One-step inward transport of a right shell obligation.

  Under the seed-window equations at radius `S (S N)`, a right
  obligation on the wider shell descends to radius `N`.
*)

Definition audit_right_shell_obligation_compactifies_one_step :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_realizes_right_shell_obligation (S N) u ->
    audit_realizes_right_shell_obligation N u :=
  right_shell_obligation_compactifies_one_step.

(*
  (35)
  Many-step inward transport of a right shell obligation.

  This iterates the preceding one-step compactification theorem: a right-side witness at radius `k + m` can be
  compactified all the way down to the smaller radius `k`.
*)

Definition audit_right_shell_obligation_compactifies_to_smaller_radius :
  forall k m u,
    audit_local_seed_window_realization (S (S (k + m))) u ->
    audit_realizes_right_shell_obligation (k + m) u ->
    audit_realizes_right_shell_obligation k u :=
  right_shell_obligation_compactifies_to_smaller_radius.

(*
  (36)
  Core-reaching compactification dichotomy.

  Starting from any radius `S (S N)`, the process ends in one of two ways:
  left persistence survives, or the right obligation reaches core radius `0`.
*)

Definition audit_local_seed_window_realization_either_left_persists_or_right_compactifies_to_core :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_far_left_hot (S N) u \/ audit_realizes_right_shell_obligation 0 u :=
  local_seed_window_realization_either_left_persists_or_right_compactifies_to_core.

(*
  (37)
  Core compactification under failure of left persistence.

  If the left branch of the preceding dichotomy is ruled out, the theorem extracts the
  right-core obligation as the only remaining possibility.
*)

Definition audit_local_seed_window_realization_without_left_persistence_compactifies_right_to_core :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    ~ audit_far_left_hot (S N) u ->
    audit_realizes_right_shell_obligation 0 u :=
  local_seed_window_realization_without_left_persistence_compactifies_right_to_core.

(*
  (38)
  Radius-two base case converting right-core pressure into left pressure.

  This is the decisive local bridge: once a right obligation reaches the
  core, the radius-two equations force far-left hotness at radius one.
*)

Definition audit_right_shell_obligation_at_core_forces_far_left_hot_one :
  forall u,
    audit_local_seed_window_realization 2 u ->
    audit_realizes_right_shell_obligation 0 u ->
    audit_far_left_hot 1 u :=
  right_shell_obligation_at_core_forces_far_left_hot_one.

(*
  (39)
  Radius-two corollary of the core bridge.

  Every legal radius-two realization already carries left pressure at
  radius one, whether it arrives there directly or through the core route.
*)

Definition audit_local_seed_window_realization_radius_two_forces_far_left_hot_one :
  forall u,
    audit_local_seed_window_realization 2 u ->
    audit_far_left_hot 1 u :=
  local_seed_window_realization_radius_two_forces_far_left_hot_one.

(*
  (40)
  Hypothetical bounded right-avoidance pattern.

  This packages the forbidden scenario where a legal realization persists
  through all levels `0..N` while avoiding left pressure everywhere.
*)

Definition audit_bounded_right_avoidance_chain :
  nat -> row -> Prop :=
  bounded_right_avoidance_chain.

(*
  (41)
  Impossibility of bounded right avoidance.

  Combining the recursive compactification with the radius-two base case
  shows that the preceding avoidance-chain scenario cannot occur.
*)

Definition audit_bounded_right_avoidance_chain_impossible :
  forall N u,
    audit_bounded_right_avoidance_chain N u ->
    False :=
  bounded_right_avoidance_chain_impossible.

(*
  (42)
  Constructive extraction of a left-persistence level.

  Instead of a bare negation, this theorem returns an explicit shell
  level `k <= N` where left pressure is forced.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_level :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    {k : nat | (k <= N)%nat /\ audit_far_left_hot (S k) u} :=
  local_seed_window_realization_forces_left_persistence_level.

(*
  (43)
  Existential version of the constructive extraction.

  This forgets the sigma-type witness of the preceding theorem and packages the result as
  an ordinary existence statement.
*)

Definition audit_local_seed_window_realization_forces_left_persistence_somewhere :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    exists k,
      (k <= N)%nat /\ audit_far_left_hot (S k) u :=
  local_seed_window_realization_forces_left_persistence_somewhere.

(*
  (44)
  Finite index type for left-obligation sites.

  An inhabitant is exactly a shell level `k` together with the proof
  that `k` lies in the bounded range `0..N`.
*)

Definition audit_bounded_left_obligation_site :
  nat -> Type :=
  bounded_left_obligation_site.

(*
  (45)
  Concrete coordinate attached to a bounded left-obligation site.

  This turns the abstract shell index from the previous bounded-obligation definition into the negative spatial
  coordinate where the corresponding hot witness will later be extracted.
*)

Definition audit_bounded_left_obligation_coord :
  forall N,
    audit_bounded_left_obligation_site N -> Z :=
  @bounded_left_obligation_coord.

(*
  (46)
  We define the bounded obligation replay object.
*)

Definition audit_bounded_obligation_replay :
  nat -> row -> Type :=
  bounded_obligation_replay.

(*
  (47)
  We record that every large enough seed-window realization builds a bounded obligation replay.
*)

Definition audit_local_seed_window_realization_builds_bounded_obligation_replay :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_obligation_replay N u :=
  local_seed_window_realization_builds_bounded_obligation_replay.

(*
  (48)
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
  (49)
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
  (50)
  We define the bounded left-obligation chain.
*)

Definition audit_bounded_left_obligation_chain :
  nat -> row -> Type :=
  bounded_left_obligation_chain.

(*
  (51)
  We record that every seed-window realization builds such a chain.
*)

Definition audit_local_seed_window_realization_builds_bounded_left_obligation_chain :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_left_obligation_chain N u :=
  local_seed_window_realization_builds_bounded_left_obligation_chain.

(*
  (52)
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
  (53)
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
  (54)
  We define the bounded left-coordinate family.
*)

Definition audit_bounded_left_coordinate_family :
  nat -> row -> Type :=
  bounded_left_coordinate_family.

(*
  (55)
  We record that every seed-window realization builds a bounded left-coordinate family.
*)

Definition audit_local_seed_window_realization_builds_bounded_left_coordinate_family :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_bounded_left_coordinate_family N u :=
  local_seed_window_realization_builds_bounded_left_coordinate_family.

(*
  (56)
  We define the left cold slab predicate.
*)

Definition audit_left_cold_slab :
  nat -> row -> Prop :=
  left_cold_slab.

(*
  (57)
  We record that a bounded left-coordinate family forbids a cold left slab.
*)

Definition audit_bounded_left_coordinate_family_implies_left_slab_nonzero :
  forall N u,
    audit_bounded_left_coordinate_family N u ->
    ~ audit_left_cold_slab N u :=
  bounded_left_coordinate_family_implies_left_slab_nonzero.

(*
  (58)
  We record the direct seed-window impossibility of a cold left slab.
*)

Definition audit_local_seed_window_realization_left_cold_slab_impossible :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    ~ audit_left_cold_slab N u :=
  local_seed_window_realization_left_cold_slab_impossible.

(*
  (59)
  We define the packaged Phase 2 memory certificate.
*)

Definition audit_phase2_memory_certificate :
  nat -> row -> Type :=
  phase2_memory_certificate.

(*
  (60)
  We record the Phase 2 endpoint: the Original Sin Theorem.
*)

Definition audit_phase2_endpoint :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_phase2_memory_certificate N u :=
  original_sin_theorem.

(*
  (60a)
  Canonical audit alias for the Phase 2 endpoint.
*)

Definition audit_original_sin_theorem :
  forall N u,
    audit_local_seed_window_realization (S (S N)) u ->
    audit_phase2_memory_certificate N u :=
  original_sin_theorem.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Original Sin Theorem                                               *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Start with a bounded realization of the seed window at     *)
(*            radius S (S N).                                            *)
(*                                                                       *)
(*    Step 2. Use the Phase 2 shell and obligation transport lemmas to   *)
(*            build a bounded left-coordinate family.                    *)
(*                                                                       *)
(*    Step 3. Deduce that the left slab [-N-3, -3] cannot be             *)
(*            identically cold.                                          *)
(*                                                                       *)
(*    Step 4. Package the coordinate family and the non-coldness         *)
(*            statement as `phase2_memory_certificate N u`.              *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    forall N u,                                                        *)
(*      `local_seed_window_realization (S (S N)) u ->`                   *)
(*      `phase2_memory_certificate N u`                                  *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Every bounded replay of the centered seed window already carries   *)
(*    a concrete left-memory certificate: a bounded family of forced     *)
(*    left coordinates, and therefore a proof that the left slab         *)
(*    [-N-3, -3] is not entirely false.                                  *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is a closed Phase 2 endpoint inside `T004`. The dependency    *)
(*    chain of `original_sin_theorem` is closed under the global context:*)
(*    no axioms and no admitted steps remain in this package.            *)
(*                                                                       *)
(*************************************************************************)

(*
  (b)
  AUXILIARY VOCABULARY
*)


(*
  (1)
  The objects below still belong to the finite Phase 2 package. They expose
  the compact-trap and hidden-support language used to organize
  reverse-side pressure, but they remain auxiliary to the closed Phase 2
  cutoff-memory endpoint above. We define the finite glitchprojection
  object first.
*)

Definition audit_glitchprojection (n k : nat) : Type :=
  glitchprojection n k.

(*
  (2)
  We define restriction of a glitchprojection to smaller width.
*)

Definition audit_glitchprojection_restrict_width :
  forall m n k,
    (m <= n)%nat ->
    audit_glitchprojection n k ->
    audit_glitchprojection m k :=
  glitchprojection_restrict_width.

(*
  (3)
  We define the profile predicate of a glitchprojection.
*)

Definition audit_glitchprojection_profile
    {n k : nat} (G : audit_glitchprojection n k) : Prop :=
  glitchprojection_profile G.

(*
  (4)
  We record classification of every glitchprojection profile.
*)

Definition audit_glitchprojection_profile_classification :
  forall n k (G : audit_glitchprojection n k),
    audit_glitchprojection_profile G :=
  glitchprojection_profile_classification.

(*
  (5)
  We record that left/right extra-side conditions force bilaterality at smaller
  width.
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
  (6)
  We record impossibility of the compact Fall trap.
*)

Definition audit_compact_fall_trap_impossible :
  forall r c,
    compact_fall_trap r c ->
    False :=
  compact_fall_trap_impossible.

(*
  (7)
  Bounded periodic replay fragment used by the auxiliary compact-trap
  vocabulary.
*)

Definition audit_bounded_periodic_replay_fragment
    (n P H : nat) : Type :=
  bounded_periodic_replay_fragment n P H.

(*
  (8)
  We define the seed-forcing glitch predicate on a bounded replay fragment.
*)

Definition audit_seed_forcing_glitch
    (n P H : nat) (F : audit_bounded_periodic_replay_fragment n P H) :
    glitch_site -> Prop :=
  seed_forcing_glitch n P H F.

(*
  (9)
  We define the compact center trap on a bounded replay fragment.
*)

Definition audit_compact_center_trap_on_fragment
    (n P H : nat) (F : audit_bounded_periodic_replay_fragment n P H)
    (g : glitch_site) : Prop :=
  compact_center_trap_on_fragment n P H F g.

(*
  (10)
  We define hidden support away from the compact center trap.
*)

Definition audit_hidden_support_at :
  row -> Z -> Z -> Prop :=
  hidden_support_at.

(*
  (11)
  We define causally relevant hidden support on a bounded replay fragment.
*)

Definition audit_causally_relevant_hidden_support
    (n P H : nat) (F : audit_bounded_periodic_replay_fragment n P H)
    (g : glitch_site) (x : Z) : Prop :=
  causally_relevant_hidden_support n P H F g x.

(*
  (12)
  We record that minimal relevant hidden support stays at distance at
  least two from the compact trap center.
*)

Definition audit_minimal_relevant_hidden_support_distance_ge_2 :
  forall n P H (F : audit_bounded_periodic_replay_fragment n P H) g d,
    minimal_relevant_hidden_support_distance n P H F g d ->
    (2 <= d)%nat :=
  minimal_relevant_hidden_support_distance_ge_2.

(*************************************************************************)
(*                                                                       *)
(*                              PHASE THREE                              *)
(*                                                                       *)
(*************************************************************************)

(*
  (iii)
  MAIN CONSTRUCTIVE FRAMEWORK: PHASE THREE
*)

(*
  (a)
  PERIODICITY AND SEMANTIC INTERFACES
*)

(*
  (1)
  We define eventual periodicity of the centered window.
*)

Definition audit_eventually_periodic_center_window :
  nat -> Prop :=
  eventually_periodic_center_window.

(*
  (2)
  We define observational periodicity from a specific cutoff and period.
*)

Definition audit_observational_periodic_tail_from :
  nat -> nat -> nat -> Prop :=
  observational_periodic_tail_from.

(*
  (3)
  We define the BHK-style upgrade principle from observation to uniformity.
*)

Definition audit_bhk_window_upgrade_principle : Prop :=
  bhk_window_upgrade_principle.

(*
  (4)
  We define the one-step semantic faithfulness principle of outward window
  growth.
*)

Definition audit_faithful_window_growth_principle : Prop :=
  faithful_window_growth_principle.

(*
  (5)
  We define a faithful observational periodic-tail realizer.
*)

Definition audit_faithful_observational_periodic_tail_realizer :
  nat -> Type :=
  faithful_observational_periodic_tail_realizer.

(*
  (6)
  We define realizable observational periodic tails at fixed width.
*)

Definition audit_realizable_observational_periodic_tail_from :
  nat -> Prop :=
  realizable_observational_periodic_tail_from.

(*
  (7)
  We define uniform eventual periodicity across all larger widths.
*)

Definition audit_uniformly_eventually_periodic_from :
  nat -> nat -> nat -> Prop :=
  uniformly_eventually_periodic_from.

(*
  (8)
  Radius-indexed realizability predicate for uniform periodic tails: there
  exists some cutoff and period witnessing uniform eventual periodicity at
  width R.
*)

Definition audit_realizable_uniform_periodic_tail_from :
  nat -> Prop :=
  realizable_uniform_periodic_tail_from.

(*
  (9)
  We define eventual periodicity of full rows from a cutoff.
*)

Definition audit_eventually_periodic_full_rows_from :
  nat -> nat -> Prop :=
  eventually_periodic_full_rows_from.

(*
  (10)
  We define a finite periodic orbit block.
*)

Definition audit_finite_periodic_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  finite_periodic_orbit.

(*
  (11)
  We define a finite repeat block.
*)

Definition audit_finite_repeat_block :
  nat -> nat -> nat -> nat -> Prop :=
  finite_repeat_block.

(*
  (b)
  CARRIER-WINDOW AND BACKWARD-TRANSPORT TOOLKIT
*)

(*
  (1)
  Centered finite window of an arbitrary row.
*)

Definition audit_row_window :
  row -> nat -> list bit :=
  row_window.

(*
  (2)
  Local realization of a target window by a predecessor row.
*)

Definition audit_local_target_window_realization :
  nat -> row -> row -> Prop :=
  local_target_window_realization.

(*
  (3)
  Predecessor carrier window at one larger radius.
*)

Definition audit_predecessor_carrier_window :
  nat -> row -> list bit :=
  predecessor_carrier_window.

(*
  (4)
  Length of a predecessor carrier window.
*)

Definition audit_predecessor_carrier_length :
  nat -> nat :=
  predecessor_carrier_length.

(*
  (5)
  Finite Rule 30 window operator on carriers.
*)

Definition audit_rule30_window :
  list bit -> list bit :=
  rule30_window.

(*
  (6)
  Recovery of the missing left bit from the Rule 30 output.
*)

Definition audit_recover_left_bit :
  bit -> bit -> bit -> bit :=
  recover_left_bit.

(*
  (7)
  Cutoff predecessor row indexed along a periodic orbit.
*)

Definition audit_cutoff_predecessor :
  nat -> nat -> nat -> row :=
  cutoff_predecessor.

(*
  (8)
  Predecessor carrier of a cutoff predecessor row.
*)

Definition audit_cutoff_predecessor_carrier :
  nat -> nat -> nat -> nat -> list bit :=
  cutoff_predecessor_carrier.

(*
  (9)
  Reversed Rule 30 window operator.
*)

Definition audit_rule30_window_rev :
  list bit -> list bit :=
  rule30_window_rev.

(*
  (10)
  Reverse reconstruction of a carrier from boundary data.
*)

Definition audit_reconstruct_carrier_rev :
  list bit -> bit -> bit -> list bit :=
  reconstruct_carrier_rev.

(*
  (11)
  When a carrier realizes a target window.
*)

Definition audit_carrier_realizes_window :
  nat -> list bit -> list bit -> Prop :=
  carrier_realizes_window.

(*
  (12)
  Canonical cutoff window at phase T.
*)

Definition audit_canonical_cutoff_window :
  nat -> nat -> list bit :=
  canonical_cutoff_window.

(*
  (13)
  We define the finite carrier-memory orbit attached to a periodic block.
*)

Definition audit_finite_carrier_memory_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  finite_carrier_memory_orbit.

(*
  (14)
  We define the one-step backward transport carrier orbit.
*)

Definition audit_backward_transport_carrier_orbit :
  nat -> nat -> nat -> nat -> Prop :=
  backward_transport_carrier_orbit.

(*
  (15)
  We define repeated predecessor carriers inside a finite orbit.
*)

Definition audit_repeated_cutoff_predecessor_carrier :
  nat -> nat -> nat -> nat -> Prop :=
  repeated_cutoff_predecessor_carrier.

(*
  (16)
  We define the finite carrier pool at a given radius.
*)

Definition audit_carrier_pool :
  nat -> list (list bit) :=
  carrier_pool.

(*
  (17)
  We record the size of the finite carrier pool.
*)

Definition audit_carrier_pool_length :
  forall R,
    length (audit_carrier_pool R) =
    Nat.pow 2 (audit_predecessor_carrier_length R) :=
  carrier_pool_length.

(*
  (18)
  We record the fixed length of every predecessor carrier window.
*)

Definition audit_predecessor_carrier_window_length :
  forall R u,
    length (audit_predecessor_carrier_window R u) =
    audit_predecessor_carrier_length R :=
  predecessor_carrier_window_length.

(*
  (19)
  We record that the recovered left bit reproduces the given Rule 30 output.
*)

Definition audit_rule30_recovers_left_bit :
  forall o b c,
    rule30 (audit_recover_left_bit o b c) b c = o :=
  rule30_recovers_left_bit.

(*
  (20)
  We record uniqueness of that recovered left bit.
*)

Definition audit_recover_left_bit_unique :
  forall a o b c,
    rule30 a b c = o ->
    a = audit_recover_left_bit o b c :=
  recover_left_bit_unique.

(*
  (21)
  We record the length of reverse carrier reconstruction.
*)

Definition audit_reconstruct_carrier_rev_from_length :
  forall outs_rev b c,
    length (reconstruct_carrier_rev_from outs_rev b c) =
    S (S (length outs_rev)) :=
  reconstruct_carrier_rev_from_length.

(*
  (22)
  We record that reverse reconstruction reproduces the prescribed outputs.
*)

Definition audit_rule30_window_rev_reconstructs_outputs :
  forall outs_rev b c,
    audit_rule30_window_rev (reconstruct_carrier_rev_from outs_rev b c) =
    outs_rev :=
  rule30_window_rev_reconstructs_outputs.

(*
  (23)
  We record boundary-based determination of the reverse carrier.
*)

Definition audit_rule30_window_rev_determined_by_boundary :
  forall outs_rev b c rest,
    audit_rule30_window_rev (c :: b :: rest) = outs_rev ->
    c :: b :: rest = reconstruct_carrier_rev_from outs_rev b c :=
  rule30_window_rev_determined_by_boundary.

(*
  (24)
  We define the two-bit right-boundary signature of a carrier.
*)

Definition audit_carrier_right_boundary_signature :
  list bit -> bit * bit :=
  carrier_right_boundary_signature.

(*
  (25)
  We record additivity of iterated row evolution.
*)

Definition audit_iter_row_plus :
  forall a b r,
    iter_row (a + b) r = iter_row a (iter_row b r) :=
  iter_row_plus.

(*
  (26)
  We record the canonical row as a shifted iterate of the automaton.
*)

Definition audit_canonical_row_after :
  forall t s,
    canonical_row (t + s)%nat = iter_row s (canonical_row t) :=
  canonical_row_after.

(*
  (27)
  We record Rule 30 evaluation on a centered predecessor carrier.
*)

Definition audit_rule30_window_on_centered_carrier :
  forall R u,
    audit_rule30_window (audit_predecessor_carrier_window R u) =
    audit_row_window (step u) R :=
  rule30_window_on_centered_carrier.

(*
  (28)
  We record weakening of centered-window equality to smaller radius.
*)

Definition audit_center_window_eq_weaken :
  forall n m t u,
    (m <= n)%nat ->
    center_window n t = center_window n u ->
    center_window m t = center_window m u :=
  center_window_eq_weaken.

(*
  (29)
  We record forward transport of a repeated larger window.
*)

Definition audit_center_window_repeat_transports_forward :
  forall radius steps a b,
    center_window (radius + steps) a = center_window (radius + steps) b ->
    center_window radius (a + steps)%nat =
    center_window radius (b + steps)%nat :=
  center_window_repeat_transports_forward.

(*
  (30)
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
  (31)
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
  (32)
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
  (33)
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
  (34)
  We record tail trimming for a finite periodic orbit block.
*)

Definition audit_finite_periodic_orbit_tail_trim :
  forall n T P K,
    audit_finite_periodic_orbit n T P (S K) ->
    audit_finite_periodic_orbit n T P K :=
  finite_periodic_orbit_tail_trim.

(*
  (35)
  We record the successor-step equality inside a finite periodic orbit.
*)

Definition audit_finite_periodic_orbit_successor_step :
  forall n T P K m,
    audit_finite_periodic_orbit n T P (S K) ->
    (m <= K)%nat ->
    center_window n (T + (S m) * P)%nat = center_window n T :=
  finite_periodic_orbit_successor_step.

(*
  (36)
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
  (37)
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
  (38)
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
  (39)
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
  (40)
  We record the carrier-memory orbit extracted from eventual periodicity.
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
  (41)
  We record that finite periodic orbits induce finite carrier-memory orbits.
*)

Definition audit_finite_periodic_orbit_implies_finite_carrier_memory_orbit :
  forall n T P K,
    audit_finite_periodic_orbit n T P (S K) ->
    audit_finite_carrier_memory_orbit n T P K :=
  finite_periodic_orbit_implies_finite_carrier_memory_orbit.

(*
  (42)
  We record one-step backward transport from a finite periodic orbit.
*)

Definition audit_finite_periodic_orbit_transports_backward_one_step :
  forall n T P K,
    audit_finite_periodic_orbit n (S T) P (S K) ->
    audit_backward_transport_carrier_orbit n T P K :=
  finite_periodic_orbit_transports_backward_one_step.

(*
  (43)
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
  (44)
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
  (45)
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
  (46)
  We record the pigeonhole step on long finite carrier-memory orbits.
*)

Definition audit_long_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (length (audit_carrier_pool R) < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  long_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (47)
  We record the repeated-carrier corollary for long finite periodic orbits.
*)

Definition audit_long_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (length (audit_carrier_pool R) < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  long_finite_periodic_orbit_has_repeated_carrier.

(*
  (48)
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
  (49)
  We record the exponential-size pigeonhole bound on finite carrier-memory orbits.
*)

Definition audit_large_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (audit_predecessor_carrier_length R) < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  large_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (50)
  We record the exponential-size repeated-carrier corollary for finite periodic orbits.
*)

Definition audit_large_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (audit_predecessor_carrier_length R) < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  large_finite_periodic_orbit_has_repeated_carrier.

(*
  (51)
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
  (52)
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
  (53)
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
  (54)
  We record that the predecessor carrier determines the target window.
*)

Definition audit_predecessor_carrier_window_determines_target_window :
  forall R u v,
    audit_predecessor_carrier_window R u =
    audit_predecessor_carrier_window R v ->
    audit_row_window (step u) R = audit_row_window (step v) R :=
  predecessor_carrier_window_determines_target_window.

(*
  (55)
  We record the exact equivalence between local target realization and Rule 30 carrier evaluation.
*)

Definition audit_local_target_window_realization_iff_rule30_window :
  forall R target u,
    audit_local_target_window_realization R target u <->
    audit_rule30_window (audit_predecessor_carrier_window R u) =
    audit_row_window target R :=
  local_target_window_realization_iff_rule30_window.

(*
  (56)
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
  (57)
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
  (58)
  We record the four-state pigeonhole step on finite carrier-memory orbits.
*)

Definition audit_small_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    audit_finite_carrier_memory_orbit R T P K ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  small_finite_carrier_memory_orbit_has_repeated_carrier.

(*
  (59)
  We record the four-state repeated-carrier corollary for finite periodic orbits.
*)

Definition audit_small_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    audit_finite_periodic_orbit R T P (S K) ->
    audit_repeated_cutoff_predecessor_carrier R T P K :=
  small_finite_periodic_orbit_has_repeated_carrier.

(*
  (60)
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
  (61)
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
  (62)
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
  (63)
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
  (64)
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
  (65)
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
  (66)
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
  (67)
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
  (68)
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
  (69)
  We record that uniform window periodicity implies full-row eventual periodicity.
*)

Definition audit_uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity :
  forall R T P,
    audit_uniformly_eventually_periodic_from R T P ->
    audit_eventually_periodic_full_rows_from T P :=
  uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity.

(*
  (70)
  We record impossibility of eventual periodicity for full canonical rows.
*)

Definition audit_eventually_periodic_full_rows_from_impossible :
  forall T P,
    audit_eventually_periodic_full_rows_from T P ->
    False :=
  eventually_periodic_full_rows_from_impossible.

(*
  (71)
  On fixed-radius uniform eventual periodicity impossibility.
  Consider how under BHK a periodicity claim is semantically significant only
  when it is given by a closed, uniform, terminating witness. The theorem below
  denies exactly such a witness for a periodic tail. It therefore does not deny that long finite stretches of repeating signatures may be
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
(*                                THEOREM                                *)
(*                                                                       *)
(*    No Uniform Periodic Tail Witness                                   *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Assume a uniform eventual-periodicity witness at           *)
(*            radius R.                                                  *)
(*                                                                       *)
(*    Step 2. Promote it to eventual periodicity of the full canonical   *)
(*            rows.                                                      *)
(*                                                                       *)
(*    Step 3. Invoke pointwise non-repetition of `canonical_row` at every*)
(*            positive lag.                                              *)
(*                                                                       *)
(*    Step 4. Conclude contradiction.                                    *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    `forall R T P,`                                                    *)
(*    `  uniformly_eventually_periodic_from R T P -> False`              *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    No closed uniform eventual-periodicity witness can exist for the   *)
(*    seeded Rule 30 orbit. Long finite or quasi-periodic behavior may   *)
(*    still be observed empirically, but it cannot be promoted to a      *)
(*    genuine infinite periodic tail by a uniform terminating witness.   *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is the strong semantic endpoint proved in Phase 3. It is the  *)
(*    recommended semantic interface for the package. It does not use    *)
(*    `replay_compactness_principle`. The unresolved conceptual step is  *)
(*    the bridge from bare fixed-width observational periodicity to      *)
(*    this stronger uniform semantic notion.                             *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*                       PHASE THREE COROLLARIES                         *)
(*                                                                       *)
(*************************************************************************)

(*
  (c)
  PHASE THREE COROLLARIES
*)

(*
  (1)
  Local realizability-theoretic corollary of the Phase 3 endpoint.

  This is the radius-indexed version of the semantic endpoint.  For each
  observation width R, the realizability predicate for a uniform periodic
  tail is empty.  The subsequent items are changes of logical form: they pass
  from the direct pointwise theorem to packaged corollaries, global
  existential negation, observational counterparts, and then the external
  bridge from semantic faithfulness to eventual aperiodicity.
*)

Definition audit_realizable_uniform_periodic_tail_from_impossible :
  forall R,
    ~ audit_realizable_uniform_periodic_tail_from R :=
  realizable_uniform_periodic_tail_from_impossible.

(*
  (1a)
  Canonical audit alias for the preferred semantic endpoint.
*)

Definition audit_phase3_semantic_endpoint :
  forall R T P,
    audit_uniformly_eventually_periodic_from R T P ->
    False :=
  uniformly_eventually_periodic_from_impossible.

(*
  (2)
  Existentially closed form of the same impossibility statement.

  Instead of fixing a radius first, this version says that there is no tuple
  of parameters witnessing any uniform eventual-periodicity claim at all.
*)

Definition audit_realizable_uniform_periodic_tail_impossible :
  ~ exists R T P, audit_uniformly_eventually_periodic_from R T P :=
  realizable_uniform_periodic_tail_impossible.

(*
  (3)
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
  (4)
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
  (5)
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
  (6)
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
  (7)
  Once the BHK upgrade is available, observational periodic tails collapse.

  The point here is that observational periodicity is not ruled out directly;
  it is ruled out after being shown to entail the stronger uniform object that
  the Phase 3 semantic endpoint has already excluded.
*)

Definition audit_observational_periodic_tail_from_impossible_under_bhk_upgrade :
  audit_bhk_window_upgrade_principle ->
  forall R T P,
    audit_observational_periodic_tail_from R T P ->
    False :=
  observational_periodic_tail_from_impossible_under_bhk_upgrade.

(*
  (8)
  Corresponding exclusion of eventual periodic center windows.

  This is the fixed-radius corollary obtained by packaging the previous tail
  statement into the standard eventual-periodicity predicate.
*)

Definition audit_eventually_periodic_center_window_impossible_under_bhk_upgrade :
  audit_bhk_window_upgrade_principle ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  eventually_periodic_center_window_impossible_under_bhk_upgrade.

(*************************************************************************)
(*                                                                       *)
(*                             1st COROLLARY                             *)
(*                                                                       *)
(*************************************************************************)

(*
  (iv)
  1ST COROLLARY
*)

(*
  (a)
  EXTERNAL FAITHFUL-SEMANTICS WRAPPER
*)

(*
  (1)
  External premise isolating the semantic bridge.

  Rather than burying this assumption inside the proof spine, the development
  names it explicitly and lets the later corollaries depend on it transparently.
*)

Definition audit_classical_semantic_faithfulness : Prop :=
  classical_semantic_faithfulness.

(*
  (2)
  Under the external premise, the BHK upgrade principle follows.
*)

Definition audit_classical_semantic_faithfulness_implies_bhk_upgrade :
  audit_classical_semantic_faithfulness ->
  audit_bhk_window_upgrade_principle :=
  classical_semantic_faithfulness_implies_bhk_upgrade.

(*
  (3)
  External classical corollary at the observational-tail level.
*)

Definition audit_classical_semantics_excludes_observational_periodic_tails :
  audit_classical_semantic_faithfulness ->
  forall R T P,
    ~ audit_observational_periodic_tail_from R T P :=
  classical_semantics_excludes_observational_periodic_tails.

(*
  (4)
  External classical corollary at the eventual-periodicity level.
*)

Definition audit_classical_semantics_excludes_eventual_periodic_windows :
  audit_classical_semantic_faithfulness ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_eventual_periodic_windows.

(*
  (4a)
  Canonical audit alias for the preferred external corollary.
*)

Definition audit_phase3_external_corollary :
  audit_classical_semantic_faithfulness ->
  forall R,
    ~ audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_eventual_periodic_windows.

(*
  (5)
  Global classical exclusion of eventual periodic center windows.

  This is the existential closure of the preceding fixed-radius statement.
*)

Definition audit_classical_semantics_excludes_any_eventual_periodic_window :
  audit_classical_semantic_faithfulness ->
  ~ exists R, audit_eventually_periodic_center_window R :=
  classical_semantics_excludes_any_eventual_periodic_window.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    No Eventually Periodic Center Window Under Faithful Semantics      *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Assume `classical_semantic_faithfulness`, i.e. faithful    *)
(*            window growth for observational periodic tails.            *)
(*                                                                       *)
(*    Step 2. Use Phase 3 to derive `bhk_window_upgrade_principle`.      *)
(*                                                                       *)
(*    Step 3. Convert any eventual periodic center window into an        *)
(*            observational periodic tail.                               *)
(*                                                                       *)
(*    Step 4. Eliminate that tail via the upgrade principle and the      *)
(*            Phase 3 semantic impossibility theorem.                    *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    `classical_semantic_faithfulness ->`                               *)
(*    `  forall R, ~ eventually_periodic_center_window R`                *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    If  one  accepts  the  external  semantic-faithfulness  premise    *)
(*    that  a genuine periodic tail must grow outward faithfully with    *)
(*    Rule 30  semantics,  then  eventual periodicity of any centered    *)
(*    window is excluded.                                                *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This lives deliberately in the external wrapper section of         *)
(*    `R04__First_Corollary` as the recommended wrapper. The premise     *)
(*    `classical_semantic_faithfulness` is not proved internally in      *)
(*    `T004`, it packages the semantic bridge cleanly instead of         *)
(*    hiding it inside the core proof spine.                             *)
(*                                                                       *)
(*************************************************************************)

(*
  (6)
  Re-export of the emptiness of the faithful observational-tail
  realizability predicate.
*)

Definition audit_faithful_observational_realizers_already_impossible :
  forall R,
    ~ audit_realizable_observational_periodic_tail_from R :=
  faithful_observational_realizers_already_impossible.

(*
  (7)
  Re-export of the emptiness of the uniform periodic-tail realizability
  predicate.
*)

Definition audit_faithful_uniform_realizers_already_impossible :
  forall R,
    ~ audit_realizable_uniform_periodic_tail_from R :=
  faithful_uniform_realizers_already_impossible.

(*************************************************************************)
(*                                                                       *)
(*                             2nd COROLLARY                             *)
(*                                                                       *)
(*************************************************************************)

(*
  (v)
  2ND COROLLARY
*)

(*
  (a)
  FINITE PROVENANCE AMBIGUITY
*)

(*
  (1)
  Finite visible shell question with the center strip removed.
*)

Definition audit_center_strip_free_manipulated :
  nat -> row -> Prop :=
  center_strip_free_manipulated.

(*
  (2)
  Decidable shell-level manipulation question.
*)

Definition audit_manipulation_question_decidable_without_center_strip :
  forall N u,
    { audit_center_strip_free_manipulated N u } +
    { ~ audit_center_strip_free_manipulated N u } :=
  manipulation_question_decidable_without_center_strip.

(*
  (3)
  Exact four-point reverse-predecessor family above a visible canonical
  observation.
*)

Definition audit_canonical_observation_has_exactly_four_reverse_predecessors :
  forall R T,
    length (canonical_reverse_predecessor_family R T) = 4%nat /\
    NoDup (canonical_reverse_predecessor_family R T) /\
    forall carrier_rev,
      reverse_predecessor_realizes_canonical_observation R T carrier_rev <->
      In carrier_rev (canonical_reverse_predecessor_family R T) :=
  canonical_observation_has_exactly_four_reverse_predecessors.

(*
  (4)
  Observation-only provenance checking is impossible.
*)

Definition audit_no_observation_only_tamper_checker :
  forall R T checker,
    ~ observation_only_tamper_checker R T checker :=
  no_observation_only_tamper_checker.

(*
  (b)
  PLAUSIBILITY
*)

(*************************************************************************)
(*                                                                       *)
(*                                RESULT                                 *)
(*                                                                       *)
(*    Linear-Effort Plausibility For The Nth Center Bit                  *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. The target value is `canonical_row n 0`, i.e. the “n-th”   *)
(*            bit of the center column. Its backward light cone has      *)
(*            depth n, so any standard local Rule 30 computation must    *)
(*            account for n layers of semantic dependence.               *)
(*                                                                       *)
(*    Step 2. A sublinear shortcut would need a bounded observational    *)
(*            summary that compresses many of those layers at once.      *)
(*                                                                       *)
(*    Step 3. The finite provenance corollary rules out exactly that     *)
(*            kind of collapse: one visible canonical observation still  *)
(*            supports an exact four-point family of hidden reverse      *)
(*            predecessors, and no checker seeing only that visible      *)
(*            observation can decide canonical versus tampered hidden    *)
(*            predecessor syntax.                                        *)
(*                                                                       *)
(*    Step 4. The earlier non-periodicity endpoints reinforce the same   *)
(*            message globally: the center strip does not collapse to a  *)
(*            closed repeating summary, and under faithful semantics     *)
(*            even eventual periodic centered windows are excluded.      *)
(*                                                                       *)
(*    Step 5. Therefore, under a standard local-semantic model of Rule   *)
(*            30 computation, the nth center bit plausibly requires      *)
(*            at least linear effort `Omega(n)`.                         *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    Under a standard local-semantic model of Rule 30 computation,      *)
(*    the nth center bit plausibly requires at least linear effort       *)
(*    `Omega(n)`.                                                        *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    The finite semantic corollaries do not by themselves prove a       *)
(*    machine lower bound, but they do show that bounded observational   *)
(*    summaries fail to collapse the hidden causal structure. That is    *)
(*    the audit-level reason linear effort is the natural complexity     *)
(*    expectation for the center column.                                 *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is intentionally an audit-level plausibility result rather    *)
(*    than a fully formal machine lower bound. `T004` does not define a  *)
(*    complete complexity model for arbitrary algorithms.  What it does  *)
(*    establish is the semantic obstruction to bounded-summary collapse  *)
(*    on which the linear-effort plausibility claim rests.               *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.

Print Assumptions the_fall.
Print Assumptions no_pure_periodicity_of_centered_windows.
Print Assumptions original_sin_theorem.
Print Assumptions uniformly_eventually_periodic_from_impossible.
Print Assumptions classical_semantics_excludes_eventual_periodic_windows.
Print Assumptions no_observation_only_tamper_checker.
