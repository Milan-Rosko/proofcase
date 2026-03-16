(* R04__Center_No_Pure_Periodicity.v *)

From Coq Require Import Classical Lia ZArith.

From T004 Require Import
  R00__Base
  R01__Seed
  R02__Local_Lemmas
  R03__Periodicity.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 1 — Compactness Contradiction              *)
(*                                                                       *)
(*  This file keeps the admissibility-to-Original-Sin contradiction      *)
(*  explicit: any admissible replay yields a candidate row above the     *)
(*  seed, hence a progenitor, contradicting Original Sin.  With the      *)
(*  repaired bounded replay layer imported from R03, it also packages    *)
(*  the compactness step from observable periodicity to the compiled     *)
(*  unconditional no-pure-periodicity theorem.                           *)
(*                                                                       *)
(*************************************************************************)

Section Center_No_Pure_Periodicity.

Definition local_seed_window_predecessor (R : nat) : Prop :=
  exists u,
    finitely_supported u /\
    forall x,
      (Z.abs x <= Z.of_nat R)%Z ->
      step u x = seed_row x.

Definition local_seed_window_model (R : nat) : row :=
  fun x =>
    if Z_lt_dec x (- Z.of_nat R - 1) then false else
    if Z_lt_dec (Z.of_nat R + 1) x then false else
    if Z.eq_dec x (-1) then false else
    if Z.eq_dec x (Z.of_nat R) then false else
    true.

Lemma local_seed_window_model_below_support :
  forall R x,
    (x < - Z.of_nat R - 1)%Z ->
    local_seed_window_model R x = false.
Proof.
  intros R x Hx.
  unfold local_seed_window_model.
  destruct (Z_lt_dec x (- Z.of_nat R - 1)) as [_ | Hcontra].
  - reflexivity.
  - lia.
Qed.

Lemma local_seed_window_model_above_support :
  forall R x,
    (Z.of_nat R + 1 < x)%Z ->
    local_seed_window_model R x = false.
Proof.
  intros R x Hx.
  unfold local_seed_window_model.
  destruct (Z_lt_dec x (- Z.of_nat R - 1)) as [Hcontra | _].
  - lia.
  - destruct (Z_lt_dec (Z.of_nat R + 1) x) as [_ | Hcontra].
    + reflexivity.
    + lia.
Qed.

Lemma local_seed_window_model_minus1 :
  forall R,
    local_seed_window_model R (-1)%Z = false.
Proof.
  intro R.
  unfold local_seed_window_model.
  destruct (Z_lt_dec (-1) (- Z.of_nat R - 1)) as [Hcontra | _].
  - lia.
  - destruct (Z_lt_dec (Z.of_nat R + 1) (-1)) as [Hcontra | _].
    + lia.
    + destruct (Z.eq_dec (-1) (-1)) as [_ | Hcontra].
      * reflexivity.
      * contradiction Hcontra; reflexivity.
Qed.

Lemma local_seed_window_model_at_R :
  forall R,
    local_seed_window_model R (Z.of_nat R) = false.
Proof.
  intro R.
  unfold local_seed_window_model.
  destruct (Z_lt_dec (Z.of_nat R) (- Z.of_nat R - 1)) as [Hcontra | _].
  - lia.
  - destruct (Z_lt_dec (Z.of_nat R + 1) (Z.of_nat R)) as [Hcontra | _].
    + lia.
    + destruct (Z.eq_dec (Z.of_nat R) (-1)) as [Hcontra | _].
      * lia.
      * destruct (Z.eq_dec (Z.of_nat R) (Z.of_nat R)) as [_ | Hcontra].
        -- reflexivity.
        -- contradiction Hcontra; reflexivity.
Qed.

Lemma local_seed_window_model_inside_true :
  forall R x,
    (- Z.of_nat R - 1 <= x <= Z.of_nat R + 1)%Z ->
    x <> (-1)%Z ->
    x <> Z.of_nat R ->
    local_seed_window_model R x = true.
Proof.
  intros R x Hrange Hneq1 HneqR.
  unfold local_seed_window_model.
  destruct (Z_lt_dec x (- Z.of_nat R - 1)) as [Hcontra | _].
  - lia.
  - destruct (Z_lt_dec (Z.of_nat R + 1) x) as [Hcontra | _].
    + lia.
    + destruct (Z.eq_dec x (-1)) as [Heq | _].
      * contradiction Hneq1; exact Heq.
      * destruct (Z.eq_dec x (Z.of_nat R)) as [Heq | _].
        -- contradiction HneqR; exact Heq.
        -- reflexivity.
Qed.

Lemma local_seed_window_model_finitely_supported :
  forall R,
    finitely_supported (local_seed_window_model R).
Proof.
  intro R.
  exists (S R).
  intros x Houtside.
  destruct Houtside as [Hleft | Hright].
  - apply local_seed_window_model_below_support.
    rewrite Nat2Z.inj_succ in Hleft.
    lia.
  - apply local_seed_window_model_above_support.
    rewrite Nat2Z.inj_succ in Hright.
    lia.
Qed.

Lemma local_seed_window_model_step_at_zero :
  forall R,
    step (local_seed_window_model R) 0%Z = seed_row 0%Z.
Proof.
  intros [|R].
  - unfold step, step_row.
    replace (0 - 1)%Z with (-1)%Z by lia.
    replace (0 + 1)%Z with 1%Z by lia.
    rewrite local_seed_window_model_minus1.
    rewrite local_seed_window_model_at_R.
    rewrite (local_seed_window_model_inside_true 0 1%Z); try lia.
    reflexivity.
  - destruct R as [|R].
    + unfold step, step_row.
      replace (0 - 1)%Z with (-1)%Z by lia.
      replace (0 + 1)%Z with 1%Z by lia.
      rewrite local_seed_window_model_minus1.
      rewrite (local_seed_window_model_inside_true 1 0%Z); try lia.
      rewrite local_seed_window_model_at_R.
      reflexivity.
    + unfold step, step_row.
      replace (0 - 1)%Z with (-1)%Z by lia.
      replace (0 + 1)%Z with 1%Z by lia.
      rewrite local_seed_window_model_minus1.
      rewrite (local_seed_window_model_inside_true (S (S R)) 0%Z); try lia.
      rewrite (local_seed_window_model_inside_true (S (S R)) 1%Z); try lia.
      reflexivity.
Qed.

Lemma local_seed_window_model_step_off_center :
  forall R x,
    (Z.abs x <= Z.of_nat R)%Z ->
    x <> 0%Z ->
    step (local_seed_window_model R) x = false.
Proof.
  intros R x Habs Hx0.
  assert (Hrange : (- Z.of_nat R <= x <= Z.of_nat R)%Z).
  {
    destruct (Zabs_spec x) as [[Hnonneg Hxeq] | [Hneg Hxeq]];
    rewrite Hxeq in Habs;
    lia.
  }
  unfold step, step_row.
  destruct (Z_lt_ge_dec x (-1)) as [Hltm1 | Hgem1].
  - assert (Hxm1_true :
        local_seed_window_model R (x - 1)%Z = true).
    {
      apply local_seed_window_model_inside_true; lia.
    }
    destruct (Z.eq_dec x (-1)) as [-> | Hxneqm1].
    + rewrite Hxm1_true.
      replace ((-1) + 1)%Z with 0%Z by lia.
      rewrite local_seed_window_model_minus1.
      rewrite (local_seed_window_model_inside_true R 0%Z); try lia.
    + assert (Hx_true :
          local_seed_window_model R x = true).
      {
        apply local_seed_window_model_inside_true; lia.
      }
      destruct (Z.eq_dec x (-2)) as [-> | Hxneqm2].
      * rewrite Hxm1_true, Hx_true.
        rewrite local_seed_window_model_minus1.
        reflexivity.
      * assert (Hxp1_true :
            local_seed_window_model R (x + 1)%Z = true).
        {
          apply local_seed_window_model_inside_true; lia.
        }
        rewrite Hxm1_true, Hx_true, Hxp1_true.
        reflexivity.
  - assert (Hm1le : (-1 <= x)%Z) by lia.
    destruct (Z.eq_dec x (-1)) as [-> | Hxneqm1].
    + replace ((-1) - 1)%Z with (-2)%Z by lia.
      rewrite (local_seed_window_model_inside_true R (-2)%Z); try lia.
      replace ((-1) + 1)%Z with 0%Z by lia.
      rewrite local_seed_window_model_minus1.
      rewrite (local_seed_window_model_inside_true R 0%Z); try lia.
      reflexivity.
    + assert (Hpos : (1 <= x)%Z) by lia.
      destruct (Z.eq_dec x (Z.of_nat R)) as [-> | HxneqR].
      * replace (Z.of_nat R - 1)%Z with (Z.of_nat R - 1)%Z by lia.
        replace (Z.of_nat R + 1)%Z with (Z.of_nat R + 1)%Z by lia.
        rewrite (local_seed_window_model_inside_true R (Z.of_nat R - 1)%Z); try lia.
        rewrite local_seed_window_model_at_R.
        rewrite (local_seed_window_model_inside_true R (Z.of_nat R + 1)%Z); try lia.
        reflexivity.
      * assert (Hx_true :
            local_seed_window_model R x = true).
        {
          apply local_seed_window_model_inside_true; lia.
        }
        destruct (Z.eq_dec x (Z.of_nat R - 1)) as [-> | HxneqR1].
        -- rewrite Hx_true.
           replace (Z.of_nat R - 1 - 1)%Z with (Z.of_nat R - 2)%Z by lia.
           replace (Z.of_nat R - 1 + 1)%Z with (Z.of_nat R)%Z by lia.
           rewrite (local_seed_window_model_inside_true R (Z.of_nat R - 2)%Z); try lia.
           rewrite local_seed_window_model_at_R.
           reflexivity.
        -- assert (Hxm1_true :
              local_seed_window_model R (x - 1)%Z = true).
           {
             apply local_seed_window_model_inside_true; lia.
           }
           assert (Hxp1_true :
              local_seed_window_model R (x + 1)%Z = true).
           {
             apply local_seed_window_model_inside_true; lia.
           }
           rewrite Hxm1_true, Hx_true, Hxp1_true.
           reflexivity.
Qed.

Theorem local_seed_window_predecessor_is_always_satisfiable :
  forall R,
    local_seed_window_predecessor R.
Proof.
  intro R.
  exists (local_seed_window_model R).
  split.
  - apply local_seed_window_model_finitely_supported.
  - intros x Habs.
    destruct (Z.eq_dec x 0%Z) as [-> | Hx0].
    + apply local_seed_window_model_step_at_zero.
    + rewrite local_seed_window_model_step_off_center; try assumption.
      symmetry.
      apply seed_row_neq_zero.
      exact Hx0.
Qed.

Theorem purely_periodic_implies_finite_replay_problem :
  forall n horizon,
    purely_periodic_center_window n ->
    finite_replay_problem n horizon.
Proof.
  intros n horizon [P [HPpos Hperiodic]].
  set (C :=
    ({| rc_period := P;
        rc_period_pos := HPpos;
        rc_space_time := canonical_row;
        rc_matches_actual := fun t => eq_refl;
        rc_replay := Hperiodic |} : replay_certificate n)).
  destruct (local_seed_window_predecessor_is_always_satisfiable
    (finite_replay_radius n horizon)) as [u [Hfs Hstep]].
  destruct Hfs as [N Hsupp].
  exists C.
  change
    (exists E : bounded_admissible_extension n horizon C,
      (forall t,
        (t <= horizon)%nat ->
        window_data (rc_space_time n C) n t = center_window n t) /\
      (forall t,
        (t + rc_period n C <= horizon)%nat ->
        window_data (rc_space_time n C) n (t + rc_period n C)%nat =
        window_data (rc_space_time n C) n t)).
  unfold C.
  simpl.
  unshelve eexists.
  - refine
      {| bae_seed_boundary := _;
         bae_upward_row := u;
         bae_support_bound := N;
         bae_support_control := Hsupp;
         bae_upward_step_legitimacy := _ |}.
    + exact canonical_row_zero.
    + intros x Hx.
      exact (Hstep x Hx).
  - split.
    + intros t _.
      reflexivity.
    + intros t _.
      exact (Hperiodic t).
Qed.

Inductive candidate_above_seed : row -> Prop :=
| candidate_above_seed_intro :
    forall n (C : replay_certificate n) (E : admissible_extension n C),
      candidate_above_seed (candidate_row_value E).

Lemma upward_admissibility_implies_candidate_row :
  forall n,
    upward_admissible n ->
    exists u, candidate_above_seed u.
Proof.
  intros n [W].
  set (C := aw_replay_certificate n W).
  set (E := aw_extension n W).
  exists (candidate_row_value E).
  now constructor.
Qed.

Lemma boundary_compatibility_gives_step_at_seed :
  forall n (C : replay_certificate n) (E : admissible_extension n C),
    forall x,
      step (candidate_row_value E) x = seed_row x.
Proof.
  intros n C E x.
  unfold candidate_row_value.
  rewrite (ae_upward_step_legitimacy n C E).
  rewrite (ae_seed_boundary n C E).
  reflexivity.
Qed.

Lemma candidate_row_respects_step :
  forall u,
    candidate_above_seed u ->
    forall x,
      step u x = seed_row x.
Proof.
  intros u [n C E] x.
  exact (boundary_compatibility_gives_step_at_seed n C E x).
Qed.

Lemma candidate_row_support_bound :
  forall u,
    candidate_above_seed u ->
    exists B,
      forall x,
        (Z.abs x > Z.of_nat B)%Z ->
        u x = false.
Proof.
  intros u [n C E].
  exists (ae_support_bound n C E).
  intros x Habs.
  unfold candidate_row_value.
  destruct (Zabs_spec x) as [[Hxnonneg Hxeq] | [Hxneg Hxeq]].
  - apply (ae_support_control n C E).
    right.
    rewrite Hxeq in Habs.
    lia.
  - apply (ae_support_control n C E).
    left.
    rewrite Hxeq in Habs.
    lia.
Qed.

Lemma candidate_row_has_finite_support :
  forall u,
    candidate_above_seed u ->
    finitely_supported u.
Proof.
  intros u Hcand.
  destruct (candidate_row_support_bound u Hcand) as [B Hbound].
  exists B.
  intros x Houtside.
  apply Hbound.
  destruct Houtside as [Hleft | Hright];
  destruct (Zabs_spec x) as [[Hxnonneg Hxeq] | [Hxneg Hxeq]];
  rewrite Hxeq; lia.
Qed.

Lemma candidate_row_is_progenitor :
  forall u,
    candidate_above_seed u ->
    progenitor u seed_row.
Proof.
  intros u Hcand.
  split.
  - apply candidate_row_has_finite_support.
    exact Hcand.
  - exact (candidate_row_respects_step u Hcand).
Qed.

Theorem upward_admissibility_implies_seed_has_progenitor :
  forall n,
    upward_admissible n ->
    exists u, progenitor u seed_row.
Proof.
  intros n Hadm.
  destruct (upward_admissibility_implies_candidate_row n Hadm) as [u Hcand].
  exists u.
  apply candidate_row_is_progenitor.
  exact Hcand.
Qed.

Theorem progenitor_contradicts_original_sin :
  (exists u, progenitor u seed_row) -> False.
Proof.
  intro Hprog.
  apply original_sin.
  exact Hprog.
Qed.

Theorem seed_cannot_be_interior :
  forall n,
    upward_admissible n -> False.
Proof.
  intros n Hadm.
  apply progenitor_contradicts_original_sin.
  apply upward_admissibility_implies_seed_has_progenitor with (n := n).
  exact Hadm.
Qed.

Theorem nonadmissibility_implies_finite_replay_obstruction :
  replay_compactness_principle ->
  forall n,
    ~ upward_admissible n ->
    exists horizon, ~ finite_replay_problem n horizon.
Proof.
  intros Hcompact n Hnot.
  destruct (classic (exists horizon, ~ finite_replay_problem n horizon))
    as [Hobstruction | Hno_obstruction].
  - exact Hobstruction.
  - exfalso.
    apply Hnot.
    apply Hcompact.
    intros horizon.
    destruct (classic (finite_replay_problem n horizon)) as [Hfinite | Hfinite].
    + exact Hfinite.
    + exfalso.
      apply Hno_obstruction.
      exists horizon.
      exact Hfinite.
Qed.

Theorem original_sin_implies_finite_replay_obstruction :
  replay_compactness_principle ->
  forall n,
    exists horizon, ~ finite_replay_problem n horizon.
Proof.
  intros Hcompact n.
  apply (nonadmissibility_implies_finite_replay_obstruction Hcompact).
  intro Hadm.
  apply (seed_cannot_be_interior n).
  exact Hadm.
Qed.

Theorem observable_periodicity_plus_upward_admissibility_implies_seed_has_progenitor :
  forall n,
    purely_periodic_center_window n ->
    upward_admissible n ->
    exists u, progenitor u seed_row.
Proof.
  intros n _ Hadm.
  apply (upward_admissibility_implies_seed_has_progenitor n).
  exact Hadm.
Qed.

Theorem observable_periodicity_plus_upward_admissibility_contradict :
  forall n,
    purely_periodic_center_window n ->
    upward_admissible n ->
    False.
Proof.
  intros n Hperiodic Hadm.
  apply progenitor_contradicts_original_sin.
  apply (observable_periodicity_plus_upward_admissibility_implies_seed_has_progenitor
    n Hperiodic Hadm).
Qed.

Theorem no_pure_periodicity_of_centered_windows :
  replay_compactness_principle ->
  forall n,
    ~ purely_periodic_center_window n.
Proof.
  intros Hcompact n Hperiodic.
  apply (seed_cannot_be_interior n).
  apply Hcompact.
  intro horizon.
  apply (purely_periodic_implies_finite_replay_problem n horizon).
  exact Hperiodic.
Qed.

Theorem center_strip_not_purely_periodic :
  replay_compactness_principle ->
  ~ purely_periodic_center_window 0%nat.
Proof.
  intro Hcompact.
  apply (no_pure_periodicity_of_centered_windows Hcompact).
Qed.

End Center_No_Pure_Periodicity.
