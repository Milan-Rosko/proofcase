(* R03__Periodicity.v *)

From Coq Require Import Arith Lia List ZArith.

From T004 Require Import
  R00__Base
  R01__Seed
  R02__Local_Lemmas.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 1 — Periodicity                            *)
(*                                                                       *)
(*  Phase 1 keeps observable periodicity separate from the replay and    *)
(*  admissibility objects used later in the contradiction scaffold.      *)
(*                                                                       *)
(*************************************************************************)

Section Periodicity.

Definition window_data (u : space_time) (n t : nat) : list bit :=
  map (u t) (centered_coords n).

(*
  Observable pure periodicity of the actual seeded run.
*)

Definition observably_pure_periodic_center_window (n P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    center_window n (t + P)%nat = center_window n t.

Definition raw_observable_periodic_center_window (n : nat) : Prop :=
  exists P, observably_pure_periodic_center_window n P.

Definition purely_periodic_center_window (n : nat) : Prop :=
  raw_observable_periodic_center_window n.

(*
  Replay data keeps only the visible repetition package.
*)

Record replay_certificate (n : nat) : Type := {
  rc_period : nat;
  rc_period_pos : (0 < rc_period)%nat;
  rc_space_time : space_time;
  rc_matches_actual :
    forall t,
      window_data rc_space_time n t = center_window n t;
  rc_replay :
    forall t,
      window_data rc_space_time n (t + rc_period)%nat =
      window_data rc_space_time n t
}.

(*
  Admissibility is a separate extension layer above replay.
*)

Record admissible_extension (n : nat) (C : replay_certificate n) : Type := {
  ae_seed_boundary :
    rc_space_time n C 0%nat = seed_row;
  ae_upward_row : row;
  ae_support_bound : nat;
  ae_support_control :
    forall x,
      (x < - Z.of_nat ae_support_bound \/
       Z.of_nat ae_support_bound < x)%Z ->
      ae_upward_row x = false;
  ae_upward_step_legitimacy :
    forall x,
      step ae_upward_row x = rc_space_time n C 0%nat x
}.

Definition candidate_row_value {n : nat} {C : replay_certificate n}
    (E : admissible_extension n C) : row :=
  ae_upward_row n C E.

Record admissibility_witness (n : nat) : Type := {
  aw_replay_certificate : replay_certificate n;
  aw_extension : admissible_extension n aw_replay_certificate
}.

Inductive upward_admissible (n : nat) : Prop :=
| upward_admissible_intro :
    forall W : admissibility_witness n,
      upward_admissible n.

Definition finite_replay_radius (n horizon : nat) : nat :=
  n + horizon.

Record bounded_admissible_extension
    (n horizon : nat) (C : replay_certificate n) : Type := {
  bae_seed_boundary :
    rc_space_time n C 0%nat = seed_row;
  bae_upward_row : row;
  bae_support_bound : nat;
  bae_support_control :
    forall x,
      (x < - Z.of_nat bae_support_bound \/
       Z.of_nat bae_support_bound < x)%Z ->
      bae_upward_row x = false;
  bae_upward_step_legitimacy :
    forall x,
      (Z.abs x <= Z.of_nat (finite_replay_radius n horizon))%Z ->
      step bae_upward_row x = rc_space_time n C 0%nat x
}.

Definition finite_replay_problem (n horizon : nat) : Prop :=
  exists C : replay_certificate n,
    exists E : bounded_admissible_extension n horizon C,
      (forall t,
        (t <= horizon)%nat ->
        window_data (rc_space_time n C) n t = center_window n t) /\
      (forall t,
        (t + rc_period n C <= horizon)%nat ->
        window_data (rc_space_time n C) n (t + rc_period n C)%nat =
        window_data (rc_space_time n C) n t).

Lemma purely_periodic_is_observable_periodicity :
  forall n,
    purely_periodic_center_window n ->
    raw_observable_periodic_center_window n.
Proof.
  intros n Hperiodic.
  exact Hperiodic.
Qed.

Lemma observable_pure_periodicity_implies_replay_certificate :
  forall n,
    raw_observable_periodic_center_window n ->
    exists C : replay_certificate n, True.
Proof.
  intros n [P [HPpos Hperiodic]].
  exists
    {| rc_period := P;
       rc_period_pos := HPpos;
       rc_space_time := canonical_row;
       rc_matches_actual := fun t => eq_refl;
       rc_replay := Hperiodic |}.
  exact I.
Qed.

Lemma admissible_extension_implies_upward_admissible :
  forall n (C : replay_certificate n),
    admissible_extension n C ->
    upward_admissible n.
Proof.
  intros n C Hext.
  refine (upward_admissible_intro n
    {| aw_replay_certificate := C;
       aw_extension := Hext |}).
Qed.

Lemma admissible_extension_implies_bounded_admissible_extension :
  forall n horizon (C : replay_certificate n),
    admissible_extension n C ->
    bounded_admissible_extension n horizon C.
Proof.
  intros n horizon C E.
  refine
    {| bae_seed_boundary := ae_seed_boundary n C E;
       bae_upward_row := ae_upward_row n C E;
       bae_support_bound := ae_support_bound n C E;
       bae_support_control := ae_support_control n C E |}.
  intros x _.
  exact (ae_upward_step_legitimacy n C E x).
Qed.

Lemma upward_admissible_implies_finite_replay_problem :
  forall n horizon,
    upward_admissible n ->
    finite_replay_problem n horizon.
Proof.
  intros n horizon [W].
  set (C := aw_replay_certificate n W).
  set (E := aw_extension n W).
  exists C.
  exists (admissible_extension_implies_bounded_admissible_extension n horizon C E).
  split.
  - intros t _.
    apply (rc_matches_actual n C).
  - intros t _.
    apply (rc_replay n C).
Qed.

Definition replay_compactness_principle : Prop :=
  forall n,
    (forall horizon, finite_replay_problem n horizon) ->
    upward_admissible n.

End Periodicity.
