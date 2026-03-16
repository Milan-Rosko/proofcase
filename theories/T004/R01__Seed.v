(* R01__Seed.v *)

From Coq Require Import Arith Bool Lia List PeanoNat ZArith.
Import ListNotations.

From T004 Require Import R00__Base.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Finite Obstruction — Seed                        *)
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
  Original Sin: the seed admits no finitely supported predecessor.
*)

Theorem original_sin :
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
  apply original_sin.
  exists (canonical_row t).
  split.
  - exact (canonical_row_finitely_supported t).
  - intro x.
    pose proof (f_equal (fun r => r x) Hseed) as Hx.
    rewrite canonical_row_step in Hx.
    exact Hx.
Qed.

End Seed_Properties.
