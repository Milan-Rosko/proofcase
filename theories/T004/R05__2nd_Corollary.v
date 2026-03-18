(* R05__2nd_Corollary.v *)

From Coq Require Import Arith Bool Classical_Prop Field Lia List Lra QArith Qreals Reals Setoid ZArith.
Import ListNotations.

From T004 Require Import
  R01__Phase_One
  R03__Phase_Three
  R04__1st_Corollary.

Open Scope Z_scope.
Open Scope Q_scope.
Open Scope R_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 2nd Corollary                                    *)
(*                                                                       *)
(*  Irrationality layer for the center column.                           *)
(*                                                                       *)
(*  The purpose of this file is to interpret the center strip as a       *)
(*  binary real, show that the finite growing-pyramid recipe yields the  *)
(*  same real, and derive a semantic irrationality consequence from the  *)
(*  radius-0 instance of the first corollary.                            *)
(*                                                                       *)
(*************************************************************************)

Section Second_Corollary.

Definition bit_value_R (b : bit) : R :=
  if b then 1 else 0.

Definition bit_value_Q (b : bit) : Q :=
  if b then 1 else 0.

Definition bit_value_Z (b : bit) : Z :=
  if b then 1%Z else 0%Z.

Lemma Z_double_match :
  forall z : Z,
    match z with
    | 0%Z => 0%Z
    | Z.pos y => Z.pos y~0
    | Z.neg y => Z.neg y~0
    end = (2 * z)%Z.
Proof.
  destruct z; reflexivity.
Qed.

Definition shift_bits (a : nat -> bit) (offset : nat) : nat -> bit :=
  fun n => a (offset + n)%nat.

Definition binary_term (a : nat -> bit) (n : nat) : R :=
  bit_value_R (a n) / 2 ^ S n.

Definition binary_prefix (a : nat -> bit) (len : nat) : R :=
  match len with
  | 0%nat => 0
  | S n => sum_f_R0 (binary_term a) n
  end.

Lemma bit_value_R_nonneg :
  forall b,
    (0 <= bit_value_R b)%R.
Proof.
  destruct b; simpl; lra.
Qed.

Lemma bit_value_R_le_1 :
  forall b,
    (bit_value_R b <= 1)%R.
Proof.
  destruct b; simpl; lra.
Qed.

Lemma bit_value_R_abs :
  forall b,
    Rabs (bit_value_R b) = bit_value_R b.
Proof.
  destruct b; simpl.
  - rewrite Rabs_R1.
    reflexivity.
  - rewrite Rabs_R0.
    reflexivity.
Qed.

Lemma binary_prefix_succ :
  forall a n,
    binary_prefix a (S n) =
    (binary_prefix a n + bit_value_R (a n) / 2 ^ S n)%R.
Proof.
  intros a [|n].
  - simpl.
    rewrite Rplus_0_l.
    reflexivity.
  - unfold binary_prefix at 1 2.
    rewrite tech5.
    reflexivity.
Qed.

Lemma binary_prefix_nonneg :
  forall a n,
    (0 <= binary_prefix a n)%R.
Proof.
  intros a n.
  induction n as [|n IH].
  - simpl.
    lra.
  - rewrite binary_prefix_succ.
    assert (Hpow : (0 < 2 ^ S n)%R).
    { apply pow_lt.
      exact Rlt_0_2. }
    assert (Hterm : (0 <= bit_value_R (a n) / 2 ^ S n)%R).
    {
      unfold Rdiv.
      apply Rmult_le_pos.
      - apply bit_value_R_nonneg.
      - left.
        apply Rinv_0_lt_compat.
        exact Hpow.
    }
    lra.
Qed.

Lemma binary_prefix_upper_bound_strong :
  forall a n,
    (binary_prefix a n <= 1 - / 2 ^ n)%R.
Proof.
  intros a n.
  induction n as [|n IH].
  - simpl.
    lra.
  - rewrite binary_prefix_succ.
    assert (Hpow : (2 ^ n <> 0)%R).
    { apply pow_nonzero.
      lra. }
    assert (Hpow_succ : (0 < 2 ^ S n)%R).
    { apply pow_lt.
      exact Rlt_0_2. }
    assert (Hterm :
      (bit_value_R (a n) / 2 ^ S n <= / 2 ^ S n)%R).
    {
      destruct (a n); simpl.
      - right.
        field.
        apply pow_nonzero.
        lra.
      - assert (Hinv : (0 <= / 2 ^ S n)%R).
        {
          left.
          apply Rinv_0_lt_compat.
          exact Hpow_succ.
        }
        unfold Rdiv.
        rewrite Rmult_0_l.
        exact Hinv.
    }
    assert (Hsplit : (1 - / 2 ^ n + / 2 ^ S n = 1 - / 2 ^ S n)%R).
    {
      replace (S n) with (n + 1)%nat by lia.
      rewrite pow_add.
      field.
      exact Hpow.
    }
    lra.
Qed.

Lemma binary_prefix_upper_bound :
  forall a n,
    (binary_prefix a n <= 1)%R.
Proof.
  intros a n.
  eapply Rle_trans.
  - apply binary_prefix_upper_bound_strong.
  - assert (Hinv : (0 <= / 2 ^ n)%R).
    {
      left.
      apply Rinv_0_lt_compat.
      apply pow_lt.
      exact Rlt_0_2.
    }
    lra.
Qed.

Lemma shift_bits_eval :
  forall a offset n,
    shift_bits a offset n = a (offset + n)%nat.
Proof.
  reflexivity.
Qed.

Lemma binary_prefix_shift_concat :
  forall a n extra,
    binary_prefix a (n + extra)%nat =
    (binary_prefix a n + binary_prefix (shift_bits a n) extra / 2 ^ n)%R.
Proof.
  intros a n extra.
  induction extra as [|extra IH].
  - rewrite Nat.add_0_r.
    simpl.
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Rplus_0_r.
    reflexivity.
  - rewrite Nat.add_succ_r.
    rewrite binary_prefix_succ.
    rewrite IH.
    rewrite binary_prefix_succ.
    rewrite shift_bits_eval.
    replace (bit_value_R (a (n + extra)%nat) / 2 ^ S (n + extra))%R
      with ((bit_value_R (a (n + extra)%nat) / 2 ^ S extra) / 2 ^ n)%R.
    + rewrite Rdiv_plus_distr by (apply pow_nonzero; lra).
      lra.
    + replace (S (n + extra)) with (n + S extra)%nat by lia.
      rewrite pow_add.
      field.
      split;
        apply pow_nonzero;
        lra.
Qed.

Lemma binary_prefix_monotone :
  forall a n m,
    (n <= m)%nat ->
    (binary_prefix a n <= binary_prefix a m)%R.
Proof.
  intros a n m Hnm.
  induction Hnm.
  - right.
    reflexivity.
  - eapply Rle_trans.
    + exact IHHnm.
    + rewrite binary_prefix_succ.
      assert (Hpow : (0 < 2 ^ S m)%R).
      { apply pow_lt.
        exact Rlt_0_2. }
      assert (Hterm : (0 <= bit_value_R (a m) / 2 ^ S m)%R).
      {
        unfold Rdiv.
        apply Rmult_le_pos.
        - apply bit_value_R_nonneg.
        - left.
          apply Rinv_0_lt_compat.
          exact Hpow.
      }
      lra.
Qed.

Lemma binary_prefix_upper_tail_bound :
  forall a n m,
    (binary_prefix a m <= binary_prefix a n + / 2 ^ n)%R.
Proof.
  intros a n m.
  destruct (le_gt_dec m n) as [Hmn | Hnm].
  - eapply Rle_trans.
    + apply (binary_prefix_monotone a m n Hmn).
    + assert (Hinv : (0 <= / 2 ^ n)%R).
      {
        left.
        apply Rinv_0_lt_compat.
        apply pow_lt.
        exact Rlt_0_2.
      }
      lra.
  - set (extra := (m - n)%nat).
    assert (Hm : m = (n + extra)%nat).
    { unfold extra.
      lia. }
    rewrite Hm.
    rewrite binary_prefix_shift_concat.
    assert (Htail :
      (binary_prefix (shift_bits a n) extra / 2 ^ n <= / 2 ^ n)%R).
    {
      assert (Hnonneg_prefix :
        (0 <= binary_prefix (shift_bits a n) extra)%R).
      { apply binary_prefix_nonneg. }
      assert (Hinv_nonneg : (0 <= / 2 ^ n)%R).
      {
        left.
        apply Rinv_0_lt_compat.
        apply pow_lt.
        exact Rlt_0_2.
      }
      unfold Rdiv.
      pose proof (binary_prefix_upper_bound (shift_bits a n) extra) as Hbound.
      nra.
    }
    lra.
Qed.

Definition binary_prefix_set (a : nat -> bit) : R -> Prop :=
  EUn (fun n => binary_prefix a n).

Lemma binary_prefix_ext :
  forall a b,
    (forall n, a n = b n) ->
    forall len,
      binary_prefix a len = binary_prefix b len.
Proof.
  intros a b Hab len.
  induction len as [|len IH].
  - reflexivity.
  - rewrite !binary_prefix_succ.
    rewrite IH.
    rewrite (Hab len).
    reflexivity.
Qed.

Lemma binary_prefix_set_ext :
  forall a b,
    (forall n, a n = b n) ->
    forall x,
      binary_prefix_set a x <-> binary_prefix_set b x.
Proof.
  intros a b Hab x.
  split; intros [n Hx]; exists n.
  - rewrite (binary_prefix_ext a b Hab n) in Hx.
    exact Hx.
  - rewrite <- (binary_prefix_ext a b Hab n) in Hx.
    exact Hx.
Qed.

Lemma binary_prefix_set_bounded :
  forall a,
    bound (binary_prefix_set a).
Proof.
  intro a.
  exists 1.
  intros x [n Hx].
  subst x.
  apply binary_prefix_upper_bound.
Qed.

Lemma binary_prefix_set_nonempty :
  forall a,
    exists x, binary_prefix_set a x.
Proof.
  intro a.
  exists 0%R.
  exists 0%nat.
  reflexivity.
Qed.

Definition binary_real_lub (a : nat -> bit) :
  { l : R | is_lub (binary_prefix_set a) l } :=
  completeness (binary_prefix_set a)
    (binary_prefix_set_bounded a)
    (binary_prefix_set_nonempty a).

Definition binary_real (a : nat -> bit) : R :=
  proj1_sig (binary_real_lub a).

Lemma binary_real_is_lub :
  forall a,
    is_lub (binary_prefix_set a) (binary_real a).
Proof.
  intro a.
  unfold binary_real.
  destruct (binary_real_lub a) as [l Hl].
  simpl.
  exact Hl.
Qed.

Lemma is_lub_ext :
  forall E F l,
    (forall x, E x <-> F x) ->
    is_lub E l ->
    is_lub F l.
Proof.
  intros E F l Hext [Hub Hleast].
  split.
  - intros x HFx.
    apply Hub.
    apply (proj2 (Hext x)).
    exact HFx.
  - intros b HubF.
    apply Hleast.
    intros x HEx.
    apply HubF.
    apply (proj1 (Hext x)).
    exact HEx.
Qed.

Lemma binary_real_ext :
  forall a b,
    (forall n, a n = b n) ->
    binary_real a = binary_real b.
Proof.
  intros a b Hab.
  eapply is_lub_u.
  - apply binary_real_is_lub.
  - apply is_lub_ext with (E := binary_prefix_set b).
    + intro x.
      symmetry.
      apply binary_prefix_set_ext.
      exact Hab.
    + apply binary_real_is_lub.
Qed.

Lemma binary_prefix_le_binary_real :
  forall a n,
    (binary_prefix a n <= binary_real a)%R.
Proof.
  intros a n.
  destruct (binary_real_is_lub a) as [Hub _].
  apply Hub.
  exists n.
  reflexivity.
Qed.

Lemma binary_real_nonneg :
  forall a,
    (0 <= binary_real a)%R.
Proof.
  intro a.
  eapply Rle_trans.
  - apply (binary_prefix_nonneg a 0%nat).
  - apply (binary_prefix_le_binary_real a 0%nat).
Qed.

Lemma binary_real_le_1 :
  forall a,
    (binary_real a <= 1)%R.
Proof.
  intro a.
  destruct (binary_real_is_lub a) as [_ Hleast].
  apply Hleast.
  intros x [n Hx].
  subst x.
  apply binary_prefix_upper_bound.
Qed.

Lemma binary_real_upper_tail_bound :
  forall a n,
    (binary_real a <= binary_prefix a n + / 2 ^ n)%R.
Proof.
  intros a n.
  destruct (binary_real_is_lub a) as [_ Hleast].
  apply Hleast.
  intros x [m Hx].
  subst x.
  apply binary_prefix_upper_tail_bound.
Qed.

Definition eventually_periodic_bits (a : nat -> bit) : Prop :=
  exists T P,
    (0 < P)%nat /\
    forall t,
      a (T + t + P)%nat = a (T + t)%nat.

Lemma eventually_periodic_bits_iff_radius0_windows :
  eventually_periodic_bits center_strip <->
  eventually_periodic_center_window 0%nat.
Proof.
  split.
  - intros [T [P [HP Hperiod]]].
    exists T, P.
    split.
    + exact HP.
    + intro t.
      rewrite center_window_width0.
      rewrite center_window_width0.
      f_equal.
      exact (Hperiod t).
  - intros [T [P [HP Hperiod]]].
    exists T, P.
    split.
    + exact HP.
    + intro t.
      specialize (Hperiod t).
      rewrite center_window_width0 in Hperiod.
      rewrite center_window_width0 in Hperiod.
      inversion Hperiod.
      reflexivity.
Qed.

Fixpoint rational_tail (a : nat -> bit) (q : Q) (n : nat) : Q :=
  match n with
  | 0%nat => q
  | S n' => (2 * rational_tail a q n' - bit_value_Q (a n'))%Q
  end.

Fixpoint tail_num (a : nat -> bit) (q : Q) (n : nat) : Z :=
  match n with
  | 0%nat => Qnum q
  | S n' =>
      (2 * tail_num a q n' - bit_value_Z (a n') * Z.pos (Qden q))%Z
  end.

Lemma rational_tail_tail_num_repr :
  forall a q n,
    rational_tail a q n == (tail_num a q n # Qden q).
Proof.
  intros a q n.
  induction n as [|n IH].
  - destruct q as [z p].
    simpl.
    reflexivity.
  - simpl.
    rewrite IH.
    destruct (a n); simpl; unfold Qeq; simpl; lia.
Qed.

Lemma binary_half_step_true :
  forall x n,
    (x / 2 ^ n = 1 / 2 ^ S n + (2 * x - 1) / 2 ^ S n)%R.
Proof.
  intros x n.
  replace (S n) with (n + 1)%nat by lia.
  rewrite pow_add.
  field.
  apply pow_nonzero.
  lra.
Qed.

Lemma binary_half_step_false :
  forall x n,
    (x / 2 ^ n = (2 * x) / 2 ^ S n)%R.
Proof.
  intros x n.
  replace (S n) with (n + 1)%nat by lia.
  rewrite pow_add.
  field.
  apply pow_nonzero.
  lra.
Qed.

Lemma Q2R_2 :
  Q2R 2 = 2%R.
Proof.
  vm_compute.
  field.
Qed.

Lemma rational_tail_real_identity :
  forall a q n,
    Q2R q =
    (binary_prefix a n + Q2R (rational_tail a q n) / 2 ^ n)%R.
Proof.
  intros a q n.
  induction n as [|n IH].
  - simpl.
    field.
  - rewrite binary_prefix_succ.
    rewrite IH.
    simpl.
    destruct (a n); simpl.
    + rewrite Q2R_minus.
      rewrite Q2R_mult.
      rewrite Q2R_2.
      rewrite RMicromega.Q2R_1.
      rewrite binary_half_step_true.
      rewrite <- Rplus_assoc.
      reflexivity.
    + rewrite Q2R_minus.
      rewrite Q2R_mult.
      rewrite Q2R_2.
      rewrite RMicromega.Q2R_0.
      replace
        (Q2R (rational_tail a q n) / 2 ^ n)%R
        with ((2 * Q2R (rational_tail a q n)) / 2 ^ S n)%R.
      2:{
        symmetry.
        apply binary_half_step_false.
      }
      rewrite Rminus_0_r.
      unfold Rdiv.
      rewrite Rmult_0_l.
      rewrite Rplus_0_r.
      reflexivity.
Qed.

Lemma rational_tail_in_unit_interval :
  forall a q n,
    binary_real a = Q2R q ->
    (0 <= Q2R (rational_tail a q n) <= 1)%R.
Proof.
  intros a q n Heq.
  pose proof (binary_prefix_le_binary_real a n) as Hlower.
  pose proof (binary_real_upper_tail_bound a n) as Hupper.
  rewrite Heq in Hlower.
  rewrite Heq in Hupper.
  rewrite (rational_tail_real_identity a q n) in Hlower.
  rewrite (rational_tail_real_identity a q n) in Hupper.
  assert (Hpow : (0 < 2 ^ n)%R).
  { apply pow_lt.
    exact Rlt_0_2. }
  assert (Hpow_nz : (2 ^ n <> 0)%R).
  { apply pow_nonzero.
    lra. }
  assert (Htail_nonneg :
    (0 <= Q2R (rational_tail a q n) / 2 ^ n)%R).
  { lra. }
  assert (Htail_le :
    (Q2R (rational_tail a q n) / 2 ^ n <= / 2 ^ n)%R).
  { lra. }
  split.
  - replace (Q2R (rational_tail a q n)) with
      ((Q2R (rational_tail a q n) / 2 ^ n) * 2 ^ n)%R.
    + apply Rmult_le_pos.
      * exact Htail_nonneg.
      * exact (Rlt_le _ _ Hpow).
    + field.
      exact Hpow_nz.
  - replace 1 with ((/ 2 ^ n) * 2 ^ n)%R.
    + replace (Q2R (rational_tail a q n)) with
        ((Q2R (rational_tail a q n) / 2 ^ n) * 2 ^ n)%R.
      * apply Rmult_le_compat_r.
        -- exact (Rlt_le _ _ Hpow).
        -- exact Htail_le.
      * field.
        exact Hpow_nz.
    + field.
      exact Hpow_nz.
Qed.

Lemma tail_num_bounds :
  forall a q n,
    binary_real a = Q2R q ->
    (0 <= tail_num a q n <= Z.pos (Qden q))%Z.
Proof.
  intros a q n Heq.
  destruct (rational_tail_in_unit_interval a q n Heq) as [Hlow Hhigh].
  replace 0%R with (Q2R 0%Q) in Hlow.
  2:{ apply RMicromega.Q2R_0. }
  replace 1%R with (Q2R 1%Q) in Hhigh.
  2:{ apply RMicromega.Q2R_1. }
  pose proof (Rle_Qle 0%Q (rational_tail a q n) Hlow) as HQlow.
  pose proof (Rle_Qle (rational_tail a q n) 1%Q Hhigh) as HQhigh.
  setoid_rewrite (rational_tail_tail_num_repr a q n) in HQlow.
  setoid_rewrite (rational_tail_tail_num_repr a q n) in HQhigh.
  unfold Qle in HQlow, HQhigh.
  simpl in HQlow, HQhigh.
  lia.
Qed.

Definition center_real : R :=
  binary_real center_strip.

Definition fueled_center_strip (n : nat) : bit :=
  fueled_rule30_row n 0%Z.

Theorem fueled_center_strip_matches_center_strip :
  forall n,
    fueled_center_strip n = center_strip n.
Proof.
  intro n.
  unfold fueled_center_strip.
  apply fueled_rule30_center_strip_matches.
Qed.

Definition fueled_center_real : R :=
  binary_real fueled_center_strip.

Theorem fueled_center_real_eq_center_real :
  fueled_center_real = center_real.
Proof.
  unfold fueled_center_real, center_real.
  apply binary_real_ext.
  exact fueled_center_strip_matches_center_strip.
Qed.

Lemma Z_to_nat_bounded_in_seq :
  forall z d,
    (0 <= z <= Z.of_nat d)%Z ->
    In (Z.to_nat z) (seq 0 (S d)).
Proof.
  intros z d [Hz0 Hzd].
  apply in_seq.
  split.
  - lia.
  - assert (Hnat : (Z.to_nat z <= d)%nat).
    {
      apply (proj2 (Nat2Z.inj_le (Z.to_nat z) d)).
      rewrite Z2Nat.id by lia.
      lia.
    }
    lia.
Qed.

Lemma tail_num_nat_in_seq :
  forall a q n,
    binary_real a = Q2R q ->
    In (Z.to_nat (tail_num a q n))
       (seq 0 (S (Z.to_nat (Z.pos (Qden q))))).
Proof.
  intros a q n Heq.
  destruct (tail_num_bounds a q n Heq) as [Hlow Hhigh].
  apply Z_to_nat_bounded_in_seq.
  split.
  - exact Hlow.
  - rewrite Z2Nat.id by lia.
    exact Hhigh.
Qed.

Lemma tail_num_to_nat_eq_implies_eq :
  forall a q i j,
    binary_real a = Q2R q ->
    Z.to_nat (tail_num a q i) = Z.to_nat (tail_num a q j) ->
    tail_num a q i = tail_num a q j.
Proof.
  intros a q i j Heq Hnat.
  destruct (tail_num_bounds a q i Heq) as [Hi0 _].
  destruct (tail_num_bounds a q j Heq) as [Hj0 _].
  apply (f_equal Z.of_nat) in Hnat.
  rewrite (Z2Nat.id (tail_num a q i) Hi0) in Hnat.
  rewrite (Z2Nat.id (tail_num a q j) Hj0) in Hnat.
  exact Hnat.
Qed.

Lemma rational_tail_has_repeated_state :
  forall a q,
    binary_real a = Q2R q ->
    exists i j,
      (i < j)%nat /\
      tail_num a q i = tail_num a q j.
Proof.
  intros a q Heq.
  set (d := Z.to_nat (Z.pos (Qden q))).
  assert (Hrep :
    exists i j,
      In i (seq 0 (S (S d))) /\
      In j (seq 0 (S (S d))) /\
      i <> j /\
      Z.to_nat (tail_num a q i) = Z.to_nat (tail_num a q j)).
  {
    apply (pigeonhole_typed nat nat Nat.eq_dec
      (fun n => Z.to_nat (tail_num a q n))
      (seq 0 (S (S d)))
      (seq 0 (S d))).
    - apply seq_NoDup.
    - intros n _.
      apply tail_num_nat_in_seq.
      exact Heq.
    - rewrite !length_seq.
      lia.
  }
  destruct Hrep as [i [j [_ [_ [Hij_neq Hsame_nat]]]]].
  destruct (lt_dec i j) as [Hij | Hji].
  - exists i, j.
    split.
    + exact Hij.
    + apply tail_num_to_nat_eq_implies_eq with (q := q).
      * exact Heq.
      * exact Hsame_nat.
  - exists j, i.
    split.
    + lia.
    + apply tail_num_to_nat_eq_implies_eq with (q := q) (i := j) (j := i).
      * exact Heq.
      * symmetry.
        exact Hsame_nat.
Qed.

Lemma equal_state_away_from_midpoint_forces_equal_step :
  forall a q i j,
    binary_real a = Q2R q ->
    tail_num a q i = tail_num a q j ->
    (2 * tail_num a q i <> Z.pos (Qden q))%Z ->
    a i = a j /\
    tail_num a q (S i) = tail_num a q (S j).
Proof.
  intros a q i j Heq Hstate Hmid.
  destruct (tail_num_bounds a q (S i) Heq) as [HSi0 HSi1].
  destruct (tail_num_bounds a q (S j) Heq) as [HSj0 HSj1].
  destruct (a i) eqn:Hbi, (a j) eqn:Hbj;
    simpl in HSi0, HSi1, HSj0, HSj1.
  - split.
    + reflexivity.
    + simpl.
      rewrite Hbi, Hbj.
      rewrite Hstate.
      reflexivity.
  - rewrite Hbi in HSi0, HSi1.
    rewrite Hbj in HSj0, HSj1.
    simpl in HSi0, HSi1, HSj0, HSj1.
    rewrite Z_double_match in HSi0, HSi1, HSj0, HSj1.
    rewrite <- Hstate in HSj0, HSj1.
    exfalso.
    apply Hmid.
    lia.
  - rewrite Hbi in HSi0, HSi1.
    rewrite Hbj in HSj0, HSj1.
    simpl in HSi0, HSi1, HSj0, HSj1.
    rewrite Z_double_match in HSi0, HSi1, HSj0, HSj1.
    rewrite <- Hstate in HSj0, HSj1.
    exfalso.
    apply Hmid.
    lia.
  - split.
    + reflexivity.
    + simpl.
      rewrite Hbi, Hbj.
      rewrite Hstate.
      reflexivity.
Qed.

Lemma repeated_state_without_midpoint_propagates :
  forall a q i j,
    binary_real a = Q2R q ->
    tail_num a q i = tail_num a q j ->
    (forall n, (2 * tail_num a q n <> Z.pos (Qden q))%Z) ->
    forall t,
      tail_num a q ((i + t)%nat) = tail_num a q ((j + t)%nat).
Proof.
  intros a q i j Heq Hstate Hnomid t.
  induction t as [|t IH].
  - rewrite !Nat.add_0_r.
    exact Hstate.
  - rewrite !Nat.add_succ_r.
    destruct
      (equal_state_away_from_midpoint_forces_equal_step
        a q ((i + t)%nat) ((j + t)%nat) Heq IH (Hnomid ((i + t)%nat)))
      as [_ Hnext].
    exact Hnext.
Qed.

Lemma tail_num_zero_forces_zero_step :
  forall a q n,
    binary_real a = Q2R q ->
    tail_num a q n = 0%Z ->
    a n = false /\
    tail_num a q (S n) = 0%Z.
Proof.
  intros a q n Heq Hzero.
  destruct (tail_num_bounds a q (S n) Heq) as [Hlow Hhigh].
  destruct (a n) eqn:Hbit.
  - assert (Hstep : tail_num a q (S n) = (- Z.pos (Qden q))%Z).
    {
      cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      rewrite Hzero.
      lia.
    }
    rewrite Hstep in Hlow.
    lia.
  - split.
    + reflexivity.
    + cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      rewrite Hzero.
      lia.
Qed.

Lemma tail_num_den_forces_one_step :
  forall a q n,
    binary_real a = Q2R q ->
    tail_num a q n = Z.pos (Qden q) ->
    a n = true /\
    tail_num a q (S n) = Z.pos (Qden q).
Proof.
  intros a q n Heq Hden.
  destruct (tail_num_bounds a q (S n) Heq) as [Hlow Hhigh].
  destruct (a n) eqn:Hbit.
  - split.
    + reflexivity.
    + cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      rewrite Hden.
      lia.
  - assert (Hstep : tail_num a q (S n) = (2 * Z.pos (Qden q))%Z).
    {
      cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      rewrite Hden.
      lia.
    }
    rewrite Hstep in Hhigh.
    lia.
Qed.

Lemma tail_num_zero_stays_zero :
  forall a q N,
    binary_real a = Q2R q ->
    tail_num a q N = 0%Z ->
    forall t,
      tail_num a q ((N + t)%nat) = 0%Z.
Proof.
  intros a q N Heq Hzero t.
  induction t as [|t IH].
  - rewrite Nat.add_0_r.
    exact Hzero.
  - rewrite Nat.add_succ_r.
    destruct (tail_num_zero_forces_zero_step a q ((N + t)%nat) Heq IH)
      as [_ Hnext].
    exact Hnext.
Qed.

Lemma tail_num_den_stays_den :
  forall a q N,
    binary_real a = Q2R q ->
    tail_num a q N = Z.pos (Qden q) ->
    forall t,
      tail_num a q ((N + t)%nat) = Z.pos (Qden q).
Proof.
  intros a q N Heq Hden t.
  induction t as [|t IH].
  - rewrite Nat.add_0_r.
    exact Hden.
  - rewrite Nat.add_succ_r.
    destruct (tail_num_den_forces_one_step a q ((N + t)%nat) Heq IH)
      as [_ Hnext].
    exact Hnext.
Qed.

Lemma tail_num_zero_bits :
  forall a q N,
    binary_real a = Q2R q ->
    tail_num a q N = 0%Z ->
    forall t,
      a ((N + t)%nat) = false.
Proof.
  intros a q N Heq Hzero t.
  destruct
    (tail_num_zero_forces_zero_step
      a q ((N + t)%nat) Heq
      (tail_num_zero_stays_zero a q N Heq Hzero t))
    as [Hbit _].
  exact Hbit.
Qed.

Lemma tail_num_den_bits :
  forall a q N,
    binary_real a = Q2R q ->
    tail_num a q N = Z.pos (Qden q) ->
    forall t,
      a ((N + t)%nat) = true.
Proof.
  intros a q N Heq Hden t.
  destruct
    (tail_num_den_forces_one_step
      a q ((N + t)%nat) Heq
      (tail_num_den_stays_den a q N Heq Hden t))
    as [Hbit _].
  exact Hbit.
Qed.

Lemma midpoint_state_yields_eventual_periodicity :
  forall a q n,
    binary_real a = Q2R q ->
    (2 * tail_num a q n = Z.pos (Qden q))%Z ->
    eventually_periodic_bits a.
Proof.
  intros a q n Heq Hmid.
  destruct (a n) eqn:Hbit.
  - assert (Hnext_zero : tail_num a q (S n) = 0%Z).
    {
      cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      lia.
    }
    exists (S n), 1%nat.
    split.
    + lia.
    + intro t.
      rewrite (tail_num_zero_bits a q (S n) Heq Hnext_zero t).
      replace (S n + t + 1)%nat with (S n + S t)%nat by lia.
      rewrite (tail_num_zero_bits a q (S n) Heq Hnext_zero (S t)).
      reflexivity.
  - assert (Hnext_den : tail_num a q (S n) = Z.pos (Qden q)).
    {
      cbn [tail_num].
      rewrite Hbit.
      cbn [bit_value_Z].
      lia.
    }
    exists (S n), 1%nat.
    split.
    + lia.
    + intro t.
      rewrite (tail_num_den_bits a q (S n) Heq Hnext_den t).
      replace (S n + t + 1)%nat with (S n + S t)%nat by lia.
      rewrite (tail_num_den_bits a q (S n) Heq Hnext_den (S t)).
      reflexivity.
Qed.

Lemma no_midpoint_rational_binary_real_eventually_periodic :
  forall a q,
    binary_real a = Q2R q ->
    (forall n, (2 * tail_num a q n <> Z.pos (Qden q))%Z) ->
    eventually_periodic_bits a.
Proof.
  intros a q Heq Hnomid.
  destruct (rational_tail_has_repeated_state a q Heq)
    as [i [j [Hij Hstate]]].
  exists i, (j - i)%nat.
  split.
  - lia.
  - intro t.
    pose proof
      (repeated_state_without_midpoint_propagates
        a q i j Heq Hstate Hnomid t) as Hstate_t.
    destruct
      (equal_state_away_from_midpoint_forces_equal_step
        a q ((i + t)%nat) ((j + t)%nat) Heq Hstate_t (Hnomid ((i + t)%nat)))
      as [Hbit _].
    replace (i + t + (j - i))%nat with (j + t)%nat by lia.
    symmetry.
    exact Hbit.
Qed.

Theorem rational_binary_real_implies_eventually_periodic_bits :
  forall a q,
    binary_real a = Q2R q ->
    eventually_periodic_bits a.
Proof.
  intros a q Heq.
  destruct (classic (exists n, (2 * tail_num a q n = Z.pos (Qden q))%Z))
    as [[n Hmid] | Hnomid].
  - exact (midpoint_state_yields_eventual_periodicity a q n Heq Hmid).
  - apply (no_midpoint_rational_binary_real_eventually_periodic a q).
    + exact Heq.
    + intros n Hmid.
      apply Hnomid.
      exists n.
      exact Hmid.
Qed.

Theorem center_real_rational_implies_eventually_periodic_bits :
  forall q,
    center_real = Q2R q ->
    eventually_periodic_bits center_strip.
Proof.
  exact (rational_binary_real_implies_eventually_periodic_bits center_strip).
Qed.

Theorem center_real_rational_implies_eventually_periodic_radius0_window :
  forall q,
    center_real = Q2R q ->
    eventually_periodic_center_window 0%nat.
Proof.
  intros q Hq.
  apply eventually_periodic_bits_iff_radius0_windows.
  exact (center_real_rational_implies_eventually_periodic_bits q Hq).
Qed.

Theorem center_real_rational_implies_cutoff_replay_package :
  forall q,
    center_real = Q2R q ->
    cutoff_replay_package 0%nat.
Proof.
  intros q Hq.
  apply eventual_periodicity_yields_cutoff_replay_package.
  exact (center_real_rational_implies_eventually_periodic_radius0_window q Hq).
Qed.

Theorem center_real_irrational_if_center_strip_not_eventually_periodic :
  ~ eventually_periodic_bits center_strip ->
  ~ exists q : Q, center_real = Q2R q.
Proof.
  intros Haper [q Hq].
  apply Haper.
  exact (center_real_rational_implies_eventually_periodic_bits q Hq).
Qed.

Theorem center_real_irrational_if_radius0_window_not_eventually_periodic :
  ~ eventually_periodic_center_window 0%nat ->
  ~ exists q : Q, center_real = Q2R q.
Proof.
  intros Haper.
  apply center_real_irrational_if_center_strip_not_eventually_periodic.
  intro Hbits.
  apply Haper.
  apply eventually_periodic_bits_iff_radius0_windows.
  exact Hbits.
Qed.

Theorem fueled_center_real_rational_implies_eventually_periodic_bits :
  forall q,
    fueled_center_real = Q2R q ->
    eventually_periodic_bits fueled_center_strip.
Proof.
  exact (rational_binary_real_implies_eventually_periodic_bits fueled_center_strip).
Qed.

Theorem fueled_center_real_rational_implies_cutoff_replay_package :
  forall q,
    fueled_center_real = Q2R q ->
    cutoff_replay_package 0%nat.
Proof.
  intros q Hq.
  apply (center_real_rational_implies_cutoff_replay_package q).
  rewrite <- fueled_center_real_eq_center_real.
  exact Hq.
Qed.

Theorem fueled_center_real_irrational_if_fueled_center_strip_not_eventually_periodic :
  ~ eventually_periodic_bits fueled_center_strip ->
  ~ exists q : Q, fueled_center_real = Q2R q.
Proof.
  intros Haper [q Hq].
  apply Haper.
  exact (fueled_center_real_rational_implies_eventually_periodic_bits q Hq).
Qed.

Theorem center_real_irrational_under_classical_semantics :
  classical_semantic_faithfulness ->
  ~ exists q : Q, center_real = Q2R q.
Proof.
  intros Hfaith.
  apply center_real_irrational_if_radius0_window_not_eventually_periodic.
  exact (classical_semantics_excludes_eventual_periodic_windows Hfaith 0%nat).
Qed.

Theorem center_real_is_not_rational_under_classical_semantics :
  classical_semantic_faithfulness ->
  forall q : Q,
    center_real <> Q2R q.
Proof.
  intros Hfaith q Hq.
  apply (center_real_irrational_under_classical_semantics Hfaith).
  exists q.
  exact Hq.
Qed.

Theorem fueled_center_real_irrational_under_classical_semantics :
  classical_semantic_faithfulness ->
  ~ exists q : Q, fueled_center_real = Q2R q.
Proof.
  intros Hfaith [q Hq].
  apply (center_real_irrational_under_classical_semantics Hfaith).
  exists q.
  rewrite <- fueled_center_real_eq_center_real.
  exact Hq.
Qed.

Theorem fueled_center_real_is_not_rational_under_classical_semantics :
  classical_semantic_faithfulness ->
  forall q : Q,
    fueled_center_real <> Q2R q.
Proof.
  intros Hfaith q Hq.
  apply (fueled_center_real_irrational_under_classical_semantics Hfaith).
  exists q.
  exact Hq.
Qed.

End Second_Corollary.
