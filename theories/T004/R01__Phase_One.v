(* R01__Phase_One.v *)

From Coq Require Import Arith Bool Classical Lia List PeanoNat ZArith.
Import ListNotations.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 1                                          *)
(*                                                                       *)
(*  Consolidated Phase 1 theory unit.  This file gathers the former      *)
(*  R00__Base through R04__No_Pure_Periodicity developments so the       *)
(*  public compile surface matches the audit synopsis exported by        *)
(*  T004__Comprehension.                                                          *)
(*                                                                       *)
(*  The Phase 1 route has four layers.                                   *)
(*                                                                       *)
(*    1. Base Rule-30 semantics on bi-infinite rows and spacetime.       *)
(*                                                                       *)
(*       We define the local update rule, global step, iteration,        *)
(*       interval agreement, and shift transport.                        *)
(*                                                                       *)
(*    2. Canonical seeded orbit.                                         *)
(*                                                                       *)
(*       We define the single-seed row, its forward orbit, centered      *)
(*       windows, and the light-cone facts needed to control that orbit. *)
(*                                                                       *)
(*    3. The No Progenitor Theorem.                                     *)
(*                                                                       *)
(*       The seed has no finitely supported predecessor.  This is the    *)
(*       rigid local contradiction that all later Phase 1 arguments      *)
(*       collapse back to.                                               *)
(*                                                                       *)
(*    4. Replay / admissibility / compactness scaffold.                  *)
(*                                                                       *)
(*       Pure periodicity is restated as a bounded replay problem at     *)
(*       every horizon.  Under replay_compactness_principle, those       *)
(*       bounded objects yield upward admissibility, hence a forbidden   *)
(*       progenitor, and therefore the no-pure-periodicity endpoint.     *)
(*                                                                       *)
(*************************************************************************)

Section Base_Definitions.

(*
  Binary state of one Rule 30 cell.
*)

Definition bit := bool.
Definition cell := bit.

(*
  Bi-infinite row indexed by Z.
*)

Definition row := Z -> cell.

(*
  Discrete spacetime indexed by time then space.
*)

Definition space_time := nat -> row.

(*
  Rule 30 local update.
*)

Definition rule30 (a b c : cell) : cell :=
  xorb a (orb b c).

(*
  One global Rule 30 update on rows.
*)

Definition step_row (r : row) : row :=
  fun x => rule30 (r (x - 1)) (r x) (r (x + 1)).

Definition step : row -> row :=
  step_row.

(*
  Iteration of the global Rule 30 update.
*)

Fixpoint iter_row (n : nat) (r : row) : row :=
  match n with
  | 0%nat => r
  | S n' => step_row (iter_row n' r)
  end.

(*
  Membership in the radius-n interval around x.
*)

Definition in_interval (x : Z) (n : nat) (y : Z) : Prop :=
  x - Z.of_nat n <= y <= x + Z.of_nat n.

(*
  Agreement of two rows on the interval [x-n, x+n].
*)

Definition same_on_interval (u v : row) (x : Z) (n : nat) : Prop :=
  forall y, in_interval x n y -> u y = v y.

(*
  Spatial shift of a row by offset k.
*)

Definition shift_row (k : Z) (r : row) : row :=
  fun x => r (x - k).

(*
  One-step evolution law.
*)

Definition evolves (u : space_time) : Prop :=
  forall t x,
    u (S t) x = rule30 (u t (x - 1)) (u t x) (u t (x + 1)).

End Base_Definitions.

Section Base_Properties.

(*
  Exhaustive truth table for Rule 30.
*)

Theorem rule30_truth_table :
  forall a b c,
    rule30 a b c =
      match a, b, c with
      | false, false, false => false
      | false, false, true => true
      | false, true, false => true
      | false, true, true => true
      | true, false, false => true
      | true, false, true => false
      | true, true, false => false
      | true, true, true => false
      end.
Proof.
  intros a b c.
  destruct a, b, c; reflexivity.
Qed.

(*
  Interval agreement can be restricted to any smaller radius.
*)

Lemma same_on_interval_weaken :
  forall u v x n m,
    (m <= n)%nat ->
    same_on_interval u v x n ->
    same_on_interval u v x m.
Proof.
  intros u v x n m Hmn Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  assert (Hmn_z : (Z.of_nat m <= Z.of_nat n)%Z).
  { apply Nat2Z.inj_le. exact Hmn. }
  lia.
Qed.

(*
  Radius (S n) agreement implies radius n agreement at the same center.
*)

Lemma same_on_interval_shift_center :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v x n.
Proof.
  intros u v x n Hsame.
  eapply same_on_interval_weaken.
  - apply Nat.le_succ_diag_r.
  - exact Hsame.
Qed.

(*
  Radius (S n) agreement around x implies radius n agreement around x-1.
*)

Lemma same_on_interval_shift_left :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v (x - 1) n.
Proof.
  intros u v x n Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(*
  Radius (S n) agreement around x implies radius n agreement around x+1.
*)

Lemma same_on_interval_shift_right :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v (x + 1) n.
Proof.
  intros u v x n Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(*
  One Rule 30 step shrinks the required agreement radius by one.
*)

Lemma step_row_locality :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval (step_row u) (step_row v) x n.
Proof.
  intros u v x n Hsame y Hy.
  unfold step_row.
  assert (Hleft : u (y - 1) = v (y - 1)).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  assert (Hmid : u y = v y).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  assert (Hright : u (y + 1) = v (y + 1)).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  rewrite Hleft, Hmid, Hright.
  reflexivity.
Qed.

(*
  Finite-speed dependence: after n steps, position x depends only on
  initial values in [x-n, x+n].
*)

Theorem iter_row_locality :
  forall n x u v,
    same_on_interval u v x n ->
    iter_row n u x = iter_row n v x.
Proof.
  induction n as [|n IH]; intros x u v Hsame.
  - simpl.
    apply Hsame.
    unfold in_interval.
    simpl.
    lia.
  - simpl.
    assert (Hleft : iter_row n u (x - 1) = iter_row n v (x - 1)).
    { apply IH.
      apply same_on_interval_shift_left.
      exact Hsame. }
    assert (Hmid : iter_row n u x = iter_row n v x).
    { apply IH.
      apply same_on_interval_shift_center.
      exact Hsame. }
    assert (Hright : iter_row n u (x + 1) = iter_row n v (x + 1)).
    { apply IH.
      apply same_on_interval_shift_right.
      exact Hsame. }
    unfold step_row.
    rewrite Hleft, Hmid, Hright.
    reflexivity.
Qed.

(*
  One-step update commutes with spatial shifts, pointwise.
*)

Lemma step_row_shift_value :
  forall r k x,
    step_row (shift_row k r) x = shift_row k (step_row r) x.
Proof.
  intros r k x.
  unfold step_row, shift_row.
  replace ((x - 1) - k) with ((x - k) - 1) by lia.
  replace ((x + 1) - k) with ((x - k) + 1) by lia.
  reflexivity.
Qed.

(*
  Iterated updates commute with spatial shifts, pointwise.
*)

Lemma iter_row_shift_value :
  forall n r k x,
    iter_row n (shift_row k r) x = shift_row k (iter_row n r) x.
Proof.
  induction n as [|n IH]; intros r k x.
  - simpl. reflexivity.
  - simpl.
    unfold step_row.
    rewrite (IH r k (x - 1)).
    rewrite (IH r k x).
    rewrite (IH r k (x + 1)).
    unfold shift_row.
    replace ((x - 1) - k) with ((x - k) - 1) by lia.
    replace ((x + 1) - k) with ((x - k) + 1) by lia.
    reflexivity.
Qed.

End Base_Properties.


(*************************************************************************)
(*                                                                       *)
(*  Canonical single-seed initial row and seed-level basic facts.        *)
(*  We define seed_row (true at 0, false elsewhere), shifted seeds,      *)
(*  and seeded trajectories.                                             *)
(*                                                                       *)
(*************************************************************************)

Section Seed_Definitions.

(*
  Single-seed initial row: true exactly at coordinate 0.
*)

Definition seed_row : row :=
  fun x => Z.eqb x 0%Z.

(*
  Shifted single-seed row, active at coordinate c.
*)

Definition shifted_seed_row (c : Z) : row :=
  shift_row c seed_row.

(*
  A trajectory is seeded when time 0 matches seed_row and the
  Rule 30 recurrence holds.
*)

Definition seeded_trajectory (u : space_time) : Prop :=
  u 0%nat = seed_row /\ evolves u.

(*
  A row is finitely supported when it vanishes outside some bounded interval.
*)

Definition finitely_supported (r : row) : Prop :=
  exists N : nat,
    forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      r x = false.

(*
  Finite-support truncation to the centered interval [-N, N].
*)

Definition truncate (N : nat) (u : row) : row :=
  fun x =>
    if Z.leb (- Z.of_nat N) x && Z.leb x (Z.of_nat N)
    then u x
    else false.

(*
  A progenitor is a finitely supported predecessor under one global step.
*)

Definition progenitor (u v : row) : Prop :=
  finitely_supported u /\
  forall x,
    step u x = v x.

(*
  Canonical single-seed trajectory.
*)

Definition canonical_row (t : nat) : row :=
  iter_row t seed_row.

(*
  Fuelled finite-support Rule 30 run.

  At stage fuel, we evolve one step and then cut back to the natural
  light-cone radius fuel.
*)

Fixpoint fueled_rule30_row (fuel : nat) : row :=
  match fuel with
  | 0%nat => seed_row
  | S fuel' => truncate (S fuel') (step (fueled_rule30_row fuel'))
  end.

Definition fueled_rule30_trajectory (fuel : nat) : space_time :=
  fun t =>
    if Nat.leb t fuel
    then fueled_rule30_row t
    else fun _ => false.

End Seed_Definitions.

Section Seed_Properties.

(*
  Seed center is active.
*)

Lemma seed_row_at_zero :
  seed_row 0%Z = true.
Proof. reflexivity. Qed.

(*
  Off-center seed cells are inactive.
*)

Lemma seed_row_neq_zero :
  forall x,
    x <> 0%Z ->
    seed_row x = false.
Proof.
  intros x Hx.
  unfold seed_row.
  apply Z.eqb_neq.
  exact Hx.
Qed.

(*
  Characterization of seed_row values.
*)

Lemma seed_row_spec :
  forall x,
    seed_row x = true <-> x = 0%Z.
Proof.
  intro x.
  unfold seed_row.
  rewrite Z.eqb_eq.
  tauto.
Qed.

(*
  Shifted seed row is active at its center.
*)

Lemma shifted_seed_row_at_center :
  forall c,
    shifted_seed_row c c = true.
Proof.
  intro c.
  unfold shifted_seed_row, shift_row.
  replace (c - c)%Z with 0%Z by lia.
  apply seed_row_at_zero.
Qed.

(*
  Shifted seed row is inactive away from its center.
*)

Lemma shifted_seed_row_off_center :
  forall c x,
    x <> c ->
    shifted_seed_row c x = false.
Proof.
  intros c x Hxc.
  unfold shifted_seed_row, shift_row.
  apply seed_row_neq_zero.
  lia.
Qed.

(*
  Canonical trajectory starts from the seed.
*)

Lemma canonical_row_zero :
  canonical_row 0%nat = seed_row.
Proof.
  reflexivity.
Qed.

(*
  Canonical trajectory evolves by one Rule 30 step.
*)

Lemma canonical_row_step :
  forall t,
    canonical_row (S t) = step (canonical_row t).
Proof.
  intro t.
  reflexivity.
Qed.

Lemma canonical_row_as_iter :
  forall t,
    canonical_row t = iter_row t seed_row.
Proof.
  intro t.
  reflexivity.
Qed.

(*
  The all-zero row is a fixed point under Rule 30 iteration.
*)

Lemma iter_row_false_row :
  forall t x,
    iter_row t (fun _ => false) x = false.
Proof.
  induction t as [|t IH]; intro x.
  - reflexivity.
  - simpl.
    unfold step_row, rule30.
    rewrite (IH (x - 1)%Z), (IH x), (IH (x + 1)%Z).
    reflexivity.
Qed.

(*
  Away from the origin, the seed row agrees with the all-zero row on the
  entire backward light cone.
*)

Lemma seed_row_agrees_with_false_away_from_origin :
  forall t x,
    (Z.of_nat t < Z.abs x)%Z ->
    same_on_interval seed_row (fun _ => false) x t.
Proof.
  intros t x Hout y Hy.
  apply seed_row_neq_zero.
  unfold in_interval in Hy.
  destruct (Zabs_spec x) as [[Hxnonneg Habs] | [Hxneg Habs]];
    rewrite Habs in Hout;
    lia.
Qed.

(*
  The canonical seeded trajectory is confined to the light cone.
*)

Lemma canonical_row_outside_light_cone :
  forall t x,
    (Z.of_nat t < Z.abs x)%Z ->
    canonical_row t x = false.
Proof.
  intros t x Hout.
  unfold canonical_row.
  rewrite (iter_row_locality t x seed_row (fun _ => false)).
  - apply iter_row_false_row.
  - exact (seed_row_agrees_with_false_away_from_origin t x Hout).
Qed.

Lemma canonical_row_finitely_supported :
  forall t,
    finitely_supported (canonical_row t).
Proof.
  intro t.
  exists t.
  intros x Hx.
  apply canonical_row_outside_light_cone.
  destruct Hx as [Hx | Hx];
  destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
    rewrite Habs;
    lia.
Qed.

Lemma truncate_outside_radius :
  forall N u x,
    (Z.of_nat N < Z.abs x)%Z ->
    truncate N u x = false.
Proof.
  intros N u x Hout.
  unfold truncate.
  destruct (Z.leb (- Z.of_nat N) x && Z.leb x (Z.of_nat N)) eqn:Hinside.
  - apply andb_true_iff in Hinside.
    destruct Hinside as [Hlb Hub].
    apply Z.leb_le in Hlb.
    apply Z.leb_le in Hub.
    destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
      rewrite Habs in Hout;
      lia.
  - reflexivity.
Qed.

Lemma truncate_inside_radius :
  forall N u x,
    (Z.abs x <= Z.of_nat N)%Z ->
    truncate N u x = u x.
Proof.
  intros N u x Hin.
  unfold truncate.
  assert (Hlb : (- Z.of_nat N <= x)%Z) by lia.
  assert (Hub : (x <= Z.of_nat N)%Z) by lia.
  assert (Hlb_bool : Z.leb (- Z.of_nat N) x = true).
  {
    apply Z.leb_le.
    exact Hlb.
  }
  assert (Hub_bool : Z.leb x (Z.of_nat N) = true).
  {
    apply Z.leb_le.
    exact Hub.
  }
  rewrite Hlb_bool, Hub_bool.
  reflexivity.
Qed.

Theorem fueled_rule30_row_matches_canonical :
  forall fuel x,
    fueled_rule30_row fuel x = canonical_row fuel x.
Proof.
  induction fuel as [|fuel IH]; intro x.
  - reflexivity.
  - simpl.
    destruct (Z_le_gt_dec (Z.abs x) (Z.of_nat (S fuel))) as [Hin | Hout].
    + rewrite truncate_inside_radius by exact Hin.
      rewrite canonical_row_step.
      unfold step, step_row.
      rewrite (IH (x - 1)%Z), (IH x), (IH (x + 1)%Z).
      reflexivity.
    + rewrite truncate_outside_radius by lia.
      symmetry.
      apply canonical_row_outside_light_cone.
      lia.
Qed.

Lemma fueled_rule30_row_finitely_supported :
  forall fuel,
    finitely_supported (fueled_rule30_row fuel).
Proof.
  intro fuel.
  exists fuel.
  intros x Hx.
  rewrite fueled_rule30_row_matches_canonical.
  apply canonical_row_outside_light_cone.
  destruct Hx as [Hx | Hx];
  destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
    rewrite Habs;
    lia.
Qed.

Lemma canonical_row_left_edge_true :
  forall t,
    canonical_row t (- Z.of_nat t)%Z = true.
Proof.
  induction t as [|t IH].
  - unfold canonical_row.
    simpl.
    change (seed_row 0%Z = true).
    exact seed_row_at_zero.
  - change ((step (canonical_row t)) (- Z.of_nat (S t))%Z = true).
    replace ((step (canonical_row t)) (- Z.of_nat (S t))%Z)
      with (rule30 (canonical_row t (- Z.of_nat t - 2)%Z)
                   (canonical_row t (- Z.of_nat t - 1)%Z)
                   (canonical_row t (- Z.of_nat t)%Z)).
    2:{
      unfold step, step_row.
      f_equal.
      - f_equal.
        lia.
      - f_equal.
        lia.
      - f_equal.
        lia.
    }
    rewrite
      (canonical_row_outside_light_cone t (- Z.of_nat t - 2)%Z),
      (canonical_row_outside_light_cone t (- Z.of_nat t - 1)%Z),
      IH.
    + reflexivity.
    + rewrite Z.abs_neq.
      * lia.
      * lia.
    + rewrite Z.abs_neq.
      * lia.
      * lia.
Qed.

Theorem canonical_row_no_repetition_pointwise :
  forall t p,
    (0 < p)%nat ->
    exists x,
      canonical_row (t + p)%nat x <> canonical_row t x.
Proof.
  intros t p Hp.
  exists (- Z.of_nat (t + p))%Z.
  rewrite canonical_row_left_edge_true.
  rewrite (canonical_row_outside_light_cone t (- Z.of_nat (t + p))%Z).
  - discriminate.
  - rewrite Z.abs_neq.
    + lia.
    + lia.
Qed.

Lemma step_false_from_two_false_inputs :
  forall r x,
    r (x - 1)%Z = false ->
    r x = false ->
    step r x = false ->
    r (x + 1)%Z = false.
Proof.
  intros r x Hleft Hmid Hstep.
  unfold step, step_row in Hstep.
  rewrite Hleft, Hmid in Hstep.
  simpl in Hstep.
  exact Hstep.
Qed.

Lemma seed_progenitor_forces_left_zero_pairs :
  forall u N,
    (forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      u x = false) ->
    (forall x,
      step u x = seed_row x) ->
    forall k,
      (k <= S N)%nat ->
      u (Z.of_nat k - Z.of_nat N - 2)%Z = false /\
      u (Z.of_nat k - Z.of_nat N - 1)%Z = false.
Proof.
  intros u N Hsupp Hstep k Hk.
  induction k as [|k IH].
  - split.
    + apply Hsupp. lia.
    + apply Hsupp. lia.
  - assert (Hk_prev : (k <= S N)%nat) by lia.
    specialize (IH Hk_prev).
    destruct IH as [Hleft Hmid].
    split.
    + replace (Z.of_nat (S k) - Z.of_nat N - 2)%Z with
        (Z.of_nat k - Z.of_nat N - 1)%Z by lia.
      exact Hmid.
    + assert (Hk_le_N : (k <= N)%nat) by lia.
      set (x := (Z.of_nat k - Z.of_nat N - 1)%Z).
      assert (Hseed_false : seed_row x = false).
      {
        apply seed_row_neq_zero.
        unfold x.
        lia.
      }
      assert (Hstep_false : step u x = false).
      {
        rewrite (Hstep x).
        exact Hseed_false.
      }
      replace (Z.of_nat (S k) - Z.of_nat N - 1)%Z with (x + 1)%Z by (unfold x; lia).
      apply (step_false_from_two_false_inputs u x).
      * unfold x.
        replace (Z.of_nat k - Z.of_nat N - 1 - 1)%Z with
          (Z.of_nat k - Z.of_nat N - 2)%Z by lia.
        exact Hleft.
      * unfold x.
        exact Hmid.
      * exact Hstep_false.
Qed.

(*
  The No Progenitor Theorem (colloquially, "the Fall"):
  the seed admits no finitely supported predecessor.
*)

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    No Progenitor Theorem                                              *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    A. Assume a finitely supported predecessor u of the seed.          *)
(*                                                                       *)
(*    B. Push the zero seed equations left-to-right along the bounded    *)
(*       support edge to force u(-1) = false and u(0) = false.           *)
(*                                                                       *)
(*    C. Evaluate the step equation at x = 0 to force u(1) = true.       *)
(*                                                                       *)
(*    D. Evaluate again at x = 1, where the seed must be false, and      *)
(*       obtain contradiction.                                           *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    ~ exists u, progenitor u seed_row                                  *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    The centered single-seed defect cannot be created in one forward   *)
(*    Rule 30 step by any finitely supported predecessor.                *)
(*                                                                       *)
(*************************************************************************)

Theorem the_fall :
  ~ exists u, progenitor u seed_row.
Proof.
  intros [u [[N Hsupp] Hstep]].
  pose proof
    (seed_progenitor_forces_left_zero_pairs u N Hsupp Hstep (S N) (le_n _))
    as [Hu_m1_false Hu_0_false].
  assert (Hu_minus1_false : u (-1)%Z = false).
  {
    replace (-1)%Z with (Z.of_nat (S N) - Z.of_nat N - 2)%Z by lia.
    exact Hu_m1_false.
  }
  assert (Hu_0_false_at_zero : u 0%Z = false).
  {
    replace 0%Z with (Z.of_nat (S N) - Z.of_nat N - 1)%Z by lia.
    exact Hu_0_false.
  }
  assert (Hu_1_true : u 1%Z = true).
  {
    pose proof (Hstep 0%Z) as Hcenter.
    unfold step, step_row in Hcenter.
    change (rule30 (u (-1)%Z) (u 0%Z) (u 1%Z) = seed_row 0%Z) in Hcenter.
    rewrite Hu_minus1_false, Hu_0_false_at_zero in Hcenter.
    rewrite seed_row_at_zero in Hcenter.
    simpl in Hcenter.
    exact Hcenter.
  }
  assert (Hseed_1_false : seed_row 1%Z = false).
  {
    apply seed_row_neq_zero.
    lia.
  }
  pose proof (Hstep 1%Z) as Hright.
  unfold step, step_row in Hright.
  change (rule30 (u 0%Z) (u 1%Z) (u 2%Z) = seed_row 1%Z) in Hright.
  rewrite Hu_0_false_at_zero, Hu_1_true in Hright.
  rewrite Hseed_1_false in Hright.
  simpl in Hright.
  discriminate.
Qed.

Theorem canonical_row_successor_not_seed :
  forall t,
    canonical_row (S t) <> seed_row.
Proof.
  intros t Hseed.
  apply the_fall.
  exists (canonical_row t).
  split.
  - exact (canonical_row_finitely_supported t).
  - intro x.
    pose proof (f_equal (fun r => r x) Hseed) as Hx.
    rewrite canonical_row_step in Hx.
    exact Hx.
Qed.

End Seed_Properties.


(*************************************************************************)
(*                                                                       *)
(*  Center-window extraction and small locality lemmas for the           *)
(*  canonical single-seed trajectory.                                    *)
(*                                                                       *)
(*************************************************************************)

Section Local_Lemmas.

(*
  Integer segment [start, start + len - 1].
*)

Fixpoint z_segment (start : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => []
  | S len' => start :: z_segment (start + 1) len'
  end.

(*
  Coordinates from -n to n.
*)

Definition centered_coords (n : nat) : list Z :=
  z_segment (- Z.of_nat n) (S (2 * n)).

(*
  Width-(2n+1) centered window cut from the canonical row at time t.
*)

Definition center_window (n t : nat) : list bit :=
  map (canonical_row t) (centered_coords n).

(*
  The center bit is the width-0 centered window.
*)

Definition center_strip (t : nat) : bit :=
  canonical_row t 0%Z.

Lemma centered_coords_width0 :
  centered_coords 0%nat = [0%Z].
Proof.
  reflexivity.
Qed.

Lemma center_window_width0 :
  forall t,
    center_window 0%nat t = [center_strip t].
Proof.
  intro t.
  unfold center_window, center_strip.
  rewrite centered_coords_width0.
  reflexivity.
Qed.

(*
  One-step update at the center.
*)

Lemma center_update :
  forall t,
    center_strip (S t) =
      rule30
        (canonical_row t (-1)%Z)
        (canonical_row t 0%Z)
        (canonical_row t 1%Z).
Proof.
  intro t.
  unfold center_strip.
  rewrite canonical_row_step.
  unfold step.
  reflexivity.
Qed.

(*
  Canonical rows depend only on the backward light cone.
*)

Lemma canonical_row_depends_on_interval :
  forall t r,
    same_on_interval r seed_row 0%Z t ->
    iter_row t r 0%Z = center_strip t.
Proof.
  intros t r Hagree.
  unfold center_strip, canonical_row.
  apply iter_row_locality.
  exact Hagree.
Qed.

(*
  The seed starts active at the center.
*)

Lemma center_strip_zero :
  center_strip 0%nat = true.
Proof.
  unfold center_strip.
  rewrite canonical_row_zero.
  exact seed_row_at_zero.
Qed.

Lemma center_window_zero :
  forall n,
    center_window n 0%nat = map seed_row (centered_coords n).
Proof.
  intro n.
  unfold center_window.
  rewrite canonical_row_zero.
  reflexivity.
Qed.

Theorem fueled_rule30_center_strip_matches :
  forall fuel,
    fueled_rule30_row fuel 0%Z = center_strip fuel.
Proof.
  intro fuel.
  unfold center_strip.
  apply fueled_rule30_row_matches_canonical.
Qed.

End Local_Lemmas.


(*************************************************************************)
(*                                                                       *)
(*  Phase 1 keeps observable periodicity separate from the replay and    *)
(*  admissibility objects used later in the contradiction scaffold.      *)
(*                                                                       *)
(*************************************************************************)

Section Periodicity.

Definition window_data (u : space_time) (n t : nat) : list bit :=
  map (u t) (centered_coords n).

Theorem fueled_rule30_trajectory_matches_canonical_prefix :
  forall fuel t x,
    (t <= fuel)%nat ->
    fueled_rule30_trajectory fuel t x = canonical_row t x.
Proof.
  intros fuel t x Htf.
  unfold fueled_rule30_trajectory.
  destruct (Nat.leb t fuel) eqn:Hle.
  - apply fueled_rule30_row_matches_canonical.
  - apply Nat.leb_gt in Hle.
    lia.
Qed.

Theorem fueled_rule30_window_matches_canonical_prefix :
  forall fuel n t,
    (t <= fuel)%nat ->
    window_data (fueled_rule30_trajectory fuel) n t = center_window n t.
Proof.
  intros fuel n t Htf.
  unfold window_data, center_window.
  apply map_ext.
  intro x.
  apply fueled_rule30_trajectory_matches_canonical_prefix.
  exact Htf.
Qed.

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


(*************************************************************************)
(*                                                                       *)
(*  Admissibility contradiction layer.                                   *)
(*                                                                       *)
(*  Any admissible replay yields a candidate row above the seed, hence   *)
(*  a progenitor, contradicting the No Progenitor Theorem.  Combined     *)
(*  replay package, this section turns pure periodicity plus compactness *)
(*  into the no-pure-periodicity endpoint.                               *)
(*                                                                       *)
(*************************************************************************)

Section No_Pure_Periodicity.

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

Theorem progenitor_contradicts_the_fall :
  (exists u, progenitor u seed_row) -> False.
Proof.
  intro Hprog.
  apply the_fall.
  exact Hprog.
Qed.

Theorem seed_cannot_be_interior :
  forall n,
    upward_admissible n -> False.
Proof.
  intros n Hadm.
  apply progenitor_contradicts_the_fall.
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

Theorem the_fall_implies_finite_replay_obstruction :
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
  apply progenitor_contradicts_the_fall.
  apply (observable_periodicity_plus_upward_admissibility_implies_seed_has_progenitor
    n Hperiodic Hadm).
Qed.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    No Pure Periodicity of Centered Windows                            *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    A. Assume pure periodicity of the radius-n centered window.        *)
(*                                                                       *)
(*    B. Convert that observation into a finite replay problem at every  *)
(*       horizon.                                                        *)
(*                                                                       *)
(*    C. Apply replay_compactness_principle to obtain upward             *)
(*       admissibility above the seed.                                   *)
(*                                                                       *)
(*    D. Use the admissibility-to-progenitor route and contradict the    *)
(*       No Progenitor Theorem.                                          *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    replay_compactness_principle ->                                    *)
(*      forall n, ~ purely_periodic_center_window n                      *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Under the compactness premise, no centered finite window of the    *)
(*    seeded Rule 30 orbit can repeat purely from time 0 onward.         *)
(*                                                                       *)
(*************************************************************************)

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

End No_Pure_Periodicity.
