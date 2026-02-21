(* R03__Beta.v *)

From Coq Require Import Arith List PeanoNat Lia ZArith Znumtheory.
Import ListNotations.
Local Open Scope nat_scope.

Definition beta (c d i : nat) : nat :=
  c mod (1 + (i + 1) * d).

Definition modulus (i d : nat) : nat :=
  1 + (i + 1) * d.

Lemma beta_eq : forall c d i, beta c d i = c mod (modulus i d).
Proof.
  reflexivity.
Qed.

Definition max_list (xs : list nat) : nat :=
  fold_right Nat.max 0 xs.

Definition beta_bound (a : list nat) : nat :=
  S (Nat.max (length a) (max_list a)).

Definition beta_d (a : list nat) : nat :=
  fact (beta_bound a).

Definition beta_mod (a : list nat) (i : nat) : nat :=
  modulus i (beta_d a).

Local Open Scope nat_scope.

Definition beta_correct (c d : nat) (a : list nat) : Prop :=
  forall i : nat,
    i < length a ->
    beta c d i = nth i a 0.

Lemma modulus_pos : forall i d, modulus i d >= 1.
Proof.
  intros i d. unfold modulus. lia.
Qed.

Lemma beta_d_pos : forall a, beta_d a > 0.
Proof.
  intro a.
  unfold beta_d.
  apply lt_O_fact.
Qed.

Lemma beta_lt_modulus : forall c d i, d > 0 -> beta c d i < modulus i d.
Proof.
  intros c d i Hd.
  unfold beta, modulus.
  apply Nat.mod_upper_bound.
  lia.
Qed.

Lemma fact_divides : forall k m, 1 <= k <= m -> Nat.divide k (fact m).
Proof.
  intros k m Hkm.
  induction m as [|m IH].
  - lia.
  - simpl.
    destruct (Nat.eq_dec k (S m)) as [Heq|Hneq].
    + subst k.
      change (Nat.divide (S m) (S m * fact m)).
      apply Nat.divide_factor_l.
    + assert (Hkm' : 1 <= k <= m) by lia.
      specialize (IH Hkm').
      apply Nat.divide_trans with (m := fact m).
      * exact IH.
      * change (Nat.divide (fact m) (S m * fact m)).
        apply Nat.divide_factor_r.
Qed.

Lemma beta_d_divisible :
  forall a k, 1 <= k <= beta_bound a -> Nat.divide k (beta_d a).
Proof.
  intros a k Hk.
  unfold beta_d.
  apply fact_divides.
  exact Hk.
Qed.

Lemma nth_le_max_list :
  forall a i, i < length a -> nth i a 0 <= max_list a.
Proof.
  induction a as [|x xs IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [|i'].
    + simpl. apply Nat.le_max_l.
    + apply Nat.le_trans with (m := nth i' xs 0).
      * apply Nat.le_refl.
      * apply Nat.le_trans with (m := max_list xs).
        -- apply IH. lia.
        -- apply Nat.le_max_r.
Qed.

Lemma fact_ge_self :
  forall n, 1 <= n -> n <= fact n.
Proof.
  intros n Hn.
  destruct n as [|n']; [lia|].
  replace (fact (S n')) with (S n' * fact n') by reflexivity.
  assert (Hf : 1 <= fact n') by (apply lt_O_fact).
  nia.
Qed.

Lemma beta_mod_gt_value :
  forall a i, i < length a -> nth i a 0 < beta_mod a i.
Proof.
  intros a i Hi.
  unfold beta_mod, modulus.
  assert (Hnth_max : nth i a 0 <= max_list a).
  { apply nth_le_max_list. exact Hi. }
  assert (Hbound_gt : max_list a < beta_bound a).
  { unfold beta_bound. lia. }
  assert (Hfact : beta_bound a <= beta_d a).
  {
    unfold beta_d.
    apply fact_ge_self.
    unfold beta_bound. lia.
  }
  assert (Hmul : 1 + beta_d a <= 1 + (i + 1) * beta_d a).
  {
    assert (Hpos : 1 <= i + 1) by lia.
    nia.
  }
  lia.
Qed.

Lemma gcd_divisor_coprime :
  forall a b q,
    Nat.divide q a ->
    Nat.gcd a b = 1 ->
    Nat.gcd q b = 1.
Proof.
  intros a b q Hqa Hg.
  assert (Hdiv : Nat.divide (Nat.gcd q b) 1).
  {
    apply Nat.divide_trans with (m := Nat.gcd a b).
    - apply Nat.gcd_greatest.
      + apply Nat.divide_trans with (m := q).
        * apply Nat.gcd_divide_l.
        * exact Hqa.
      + apply Nat.gcd_divide_r.
    - rewrite Hg. apply Nat.divide_refl.
  }
  apply Nat.divide_1_r in Hdiv.
  exact Hdiv.
Qed.

Lemma modulus_coprime_of_divisibility_lt :
  forall n d i j,
    (forall k, 1 <= k <= n -> Nat.divide k d) ->
    i < n ->
    j < n ->
    i < j ->
    Nat.gcd (modulus i d) (modulus j d) = 1.
Proof.
  intros n d i j Hdiv Hi Hj Hij.
  set (mi := modulus i d).
    set (mj := modulus j d).
    set (g := Nat.gcd mi mj).
    assert (Hgmi : Nat.divide g mi) by (unfold g; apply Nat.gcd_divide_l).
    assert (Hgmj : Nat.divide g mj) by (unfold g; apply Nat.gcd_divide_r).
    assert (Hgdiff : Nat.divide g (mj - mi)).
    { apply Nat.divide_sub_r; assumption. }
    assert (Hdiff : mj - mi = (j - i) * d).
    {
      unfold mi, mj, modulus.
      replace (1 + (j + 1) * d - (1 + (i + 1) * d))
        with ((j + 1) * d - (i + 1) * d) by lia.
      rewrite Nat.mul_sub_distr_r.
      lia.
    }
    rewrite Hdiff in Hgdiff.
    assert (Hgcdgd1 : Nat.gcd g d = 1).
    {
      apply Nat.gcd_unique.
      - apply Nat.divide_1_l.
      - apply Nat.divide_1_l.
      - intros q Hqg Hqd.
        assert (Hqmi : Nat.divide q mi).
        { apply Nat.divide_trans with (m := g); assumption. }
        assert (Hqterm : Nat.divide q ((i + 1) * d)).
        { apply Nat.divide_mul_r. exact Hqd. }
        assert (Hq1 : Nat.divide q (mi - (i + 1) * d)).
        { apply Nat.divide_sub_r; assumption. }
        replace (mi - (i + 1) * d) with 1 in Hq1 by (unfold mi, modulus; lia).
        exact Hq1.
    }
    assert (Hgji : Nat.divide g (j - i)).
    {
      apply Nat.gauss with (m := d).
      - rewrite Nat.mul_comm. exact Hgdiff.
      - exact Hgcdgd1.
    }
    assert (Hjid : Nat.divide (j - i) d).
    { apply Hdiv. lia. }
    assert (Hgd : Nat.divide g d).
    { apply Nat.divide_trans with (m := j - i); assumption. }
    assert (Hg1 : g = 1).
    {
      apply (proj1 (Nat.divide_gcd_iff g d)) in Hgd.
      rewrite Hgcdgd1 in Hgd.
      exact (eq_sym Hgd).
    }
    unfold g, mi, mj in Hg1.
    exact Hg1.
Qed.

Lemma modulus_coprime_of_divisibility :
  forall n d i j,
    (forall k, 1 <= k <= n -> Nat.divide k d) ->
    i < n ->
    j < n ->
    i <> j ->
    Nat.gcd (modulus i d) (modulus j d) = 1.
Proof.
  intros n d i j Hdiv Hi Hj Hneq.
  destruct (Nat.lt_total i j) as [Hij|Hcase].
  - apply (modulus_coprime_of_divisibility_lt n d i j Hdiv Hi Hj Hij).
  - assert (Hji : j < i) by lia.
    rewrite Nat.gcd_comm.
    apply (modulus_coprime_of_divisibility_lt n d j i Hdiv Hj Hi Hji).
Qed.

Lemma beta_mod_coprime :
  forall a i j,
    i < length a -> j < length a -> i <> j ->
    Nat.gcd (beta_mod a i) (beta_mod a j) = 1.
Proof.
  intros a i j Hi Hj Hneq.
  unfold beta_mod.
  apply modulus_coprime_of_divisibility with (n := beta_bound a).
  - intros k Hk. apply beta_d_divisible. exact Hk.
  - unfold beta_bound. lia.
  - unfold beta_bound. lia.
  - exact Hneq.
Qed.

Lemma crt_two :
  forall m1 m2 r1 r2 : nat,
    m1 > 0 -> m2 > 0 ->
    Nat.gcd m1 m2 = 1 ->
    exists c, c mod m1 = r1 mod m1 /\ c mod m2 = r2 mod m2.
Proof.
  intros m1 m2 r1 r2 Hm1 Hm2 Hg.
  pose proof (Nat.gcd_bezout_pos_pos m1 Hm1 m2 Hm2) as [Hb12 Hb21].
  rewrite Hg in Hb12, Hb21.
  destruct Hb12 as [u1 [v1 Hu1]].
  destruct Hb21 as [u2 [v2 Hu2]].
  exists (r1 * u2 * m2 + r2 * u1 * m1).
  split.
  - rewrite Nat.Div0.add_mod by lia.
    assert (Hleft : (r1 * u2 * m2) mod m1 = r1 mod m1).
    {
      rewrite <- Nat.mul_assoc.
      rewrite Hu2.
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.Div0.add_mod by lia.
      rewrite Nat.mul_assoc.
      rewrite Nat.Div0.mod_mul by lia.
      rewrite Nat.add_0_r.
      rewrite Nat.mul_1_r.
      rewrite Nat.Div0.mod_mod by lia.
      reflexivity.
    }
    assert (Hright : (r2 * u1 * m1) mod m1 = 0).
    {
      replace (r2 * u1 * m1) with ((r2 * u1) * m1) by lia.
      rewrite Nat.Div0.mod_mul by lia.
      reflexivity.
    }
    rewrite Hleft, Hright.
    rewrite Nat.add_0_r.
    rewrite Nat.Div0.mod_mod by lia.
    reflexivity.
  - rewrite Nat.Div0.add_mod by lia.
    assert (Hleft : (r2 * u1 * m1) mod m2 = r2 mod m2).
    {
      rewrite <- Nat.mul_assoc.
      rewrite Hu1.
      rewrite Nat.mul_add_distr_l.
      rewrite Nat.Div0.add_mod by lia.
      rewrite Nat.mul_assoc.
      rewrite Nat.Div0.mod_mul by lia.
      rewrite Nat.add_0_r.
      rewrite Nat.mul_1_r.
      rewrite Nat.Div0.mod_mod by lia.
      reflexivity.
    }
    assert (Hright : (r1 * u2 * m2) mod m2 = 0).
    {
      replace (r1 * u2 * m2) with ((r1 * u2) * m2) by lia.
      rewrite Nat.Div0.mod_mul by lia.
      reflexivity.
    }
    rewrite Hright, Hleft.
    rewrite Nat.add_0_l.
    rewrite Nat.Div0.mod_mod by lia.
    reflexivity.
Qed.

Lemma nth_default_irrel :
  forall (A : Type) (l : list A) i d1 d2,
    i < length l ->
    nth i l d1 = nth i l d2.
Proof.
  intros A l.
  induction l as [|x xs IH]; intros i d1 d2 Hi; simpl in *.
  - lia.
  - destruct i as [|i'].
    + reflexivity.
    + apply IH. lia.
Qed.

Lemma fold_mul_pos :
  forall ms,
    (forall i, i < length ms -> nth i ms 0 > 0) ->
    fold_right Nat.mul 1 ms > 0.
Proof.
  induction ms as [|m ms IH]; intros Hpos; simpl.
  - lia.
  - assert (Hm : m > 0) by (apply (Hpos 0); simpl; lia).
    assert (Hrest : fold_right Nat.mul 1 ms > 0).
    {
      apply IH.
      intros i Hi.
      apply (Hpos (S i)).
      simpl. lia.
    }
    apply Nat.mul_pos_pos; assumption.
Qed.

Lemma nth_divides_prod :
  forall i ms,
    i < length ms ->
    Nat.divide (nth i ms 0) (fold_right Nat.mul 1 ms).
Proof.
  intros i ms Hi.
  revert i Hi.
  induction ms as [|m ms IH]; intros i Hi; simpl in *.
  - lia.
  - destruct i as [|i'].
    + simpl. apply Nat.divide_factor_l.
    + specialize (IH i' ltac:(lia)).
      apply Nat.divide_trans with (m := fold_right Nat.mul 1 ms).
      * exact IH.
      * apply Nat.divide_factor_r.
Qed.

Lemma mod_divides_transfer :
  forall c c' m M,
    m > 0 ->
    M > 0 ->
    Nat.divide m M ->
    c mod M = c' mod M ->
    c mod m = c' mod m.
Proof.
  intros c c' m M Hm HM [k Hk] Hmod.
  subst M.
  assert (Hk : k > 0) by nia.
  assert (Hmk : m * k > 0) by nia.
  apply Nat2Z.inj.
  rewrite !Nat2Z.inj_mod by lia.
  assert (Hzmod :
    (Z.of_nat c mod Z.of_nat (m * k))%Z =
    (Z.of_nat c' mod Z.of_nat (m * k))%Z).
  {
    apply (f_equal Z.of_nat) in Hmod.
    rewrite !Nat2Z.inj_mod in Hmod by lia.
    rewrite Nat.mul_comm in Hmod.
    exact Hmod.
  }
  rewrite (Zmod_div_mod (Z.of_nat m) (Z.of_nat (m * k)) (Z.of_nat c))%Z.
  2:{ apply (proj1 (Nat2Z.inj_lt 0 m)). lia. }
  2:{ apply (proj1 (Nat2Z.inj_lt 0 (m * k))). lia. }
  2:{
    exists (Z.of_nat k).
    rewrite Nat2Z.inj_mul.
    lia.
  }
  rewrite (Zmod_div_mod (Z.of_nat m) (Z.of_nat (m * k)) (Z.of_nat c'))%Z.
  2:{ apply (proj1 (Nat2Z.inj_lt 0 m)). lia. }
  2:{ apply (proj1 (Nat2Z.inj_lt 0 (m * k))). lia. }
  2:{
    exists (Z.of_nat k).
    rewrite Nat2Z.inj_mul.
    lia.
  }
  apply (f_equal (fun z => (z mod Z.of_nat m)%Z)) in Hzmod.
  exact Hzmod.
Qed.

Lemma coprime_fold_mul :
  forall m ms,
    (forall i, i < length ms -> Nat.gcd m (nth i ms 0) = 1) ->
    Nat.gcd m (fold_right Nat.mul 1 ms) = 1.
Proof.
  intros m ms.
  induction ms as [|m' ms' IH]; intros Hco.
  - simpl.
    apply Nat.gcd_unique.
    + apply Nat.divide_1_l.
    + apply Nat.divide_refl.
    + intros q _ Hq1.
      exact Hq1.
  - simpl.
    assert (Hm0 : Nat.gcd m m' = 1).
    {
      specialize (Hco 0).
      simpl in Hco.
      apply Hco.
      lia.
    }
    assert (Hrest : Nat.gcd m (fold_right Nat.mul 1 ms') = 1).
    {
      apply IH.
      intros i Hi.
      specialize (Hco (S i)).
      simpl in Hco.
      apply Hco.
      simpl. lia.
    }
    apply Nat.gcd_unique.
    + apply Nat.divide_1_l.
    + apply Nat.divide_1_l.
    + intros q Hqm Hqprod.
      assert (Hq_coprime_m' : Nat.gcd q m' = 1).
      { apply gcd_divisor_coprime with (a := m) (b := m'); assumption. }
      assert (Hqrest : Nat.divide q (fold_right Nat.mul 1 ms')).
      {
        apply Nat.gauss with (m := m').
        - exact Hqprod.
        - exact Hq_coprime_m'.
      }
      assert (Hq1 : Nat.divide q 1).
      {
        apply Nat.divide_trans with (m := Nat.gcd m (fold_right Nat.mul 1 ms')).
        - apply Nat.gcd_greatest; assumption.
        - rewrite Hrest. apply Nat.divide_refl.
      }
      exact Hq1.
Qed.

Lemma crt_list :
  forall (ms rs : list nat),
    length ms = length rs ->
    (forall i, i < length ms -> nth i ms 0 > 0) ->
    (forall i j, i < length ms -> j < length ms -> i <> j ->
       Nat.gcd (nth i ms 0) (nth j ms 0) = 1) ->
    exists c, forall i, i < length ms ->
      c mod (nth i ms 0) = (nth i rs 0) mod (nth i ms 0).
Proof.
  induction ms as [|m ms IH]; intros rs Hlen Hpos Hpair.
  - destruct rs as [|r rs']; simpl in Hlen; try discriminate.
    exists 0.
    intros i Hi. inversion Hi.
  - destruct rs as [|r rs']; simpl in Hlen; try discriminate.
    inversion Hlen as [Hlen'].
    assert (Hmpos : m > 0) by (apply (Hpos 0); simpl; lia).
    assert (Hpos_tail : forall i, i < length ms -> nth i ms 0 > 0).
    {
      intros i Hi.
      apply (Hpos (S i)).
      simpl. lia.
    }
    assert (Hpair_tail :
      forall i j, i < length ms -> j < length ms -> i <> j ->
        Nat.gcd (nth i ms 0) (nth j ms 0) = 1).
    {
      intros i j Hi Hj Hij.
      apply (Hpair (S i) (S j)); simpl; lia.
    }
    destruct (IH rs' Hlen' Hpos_tail Hpair_tail) as [c' Hc'].
    set (M' := fold_right Nat.mul 1 ms).
    assert (HMpos : M' > 0).
    {
      unfold M'. apply fold_mul_pos. exact Hpos_tail.
    }
    assert (Hcop_head_each : forall i, i < length ms -> Nat.gcd m (nth i ms 0) = 1).
    {
      intros i Hi.
      apply (Hpair 0 (S i)); simpl; lia.
    }
    assert (Hgcd_mM : Nat.gcd m M' = 1).
    {
      unfold M'. apply coprime_fold_mul. exact Hcop_head_each.
    }
    destruct (crt_two m M' r c' Hmpos HMpos Hgcd_mM) as [c [Hcm HcM]].
    exists c.
    intros i Hi.
    destruct i as [|i'].
    + simpl. exact Hcm.
    + simpl.
      assert (Hi' : i' < length ms).
      { apply Nat.succ_lt_mono. exact Hi. }
      assert (Hdiv : Nat.divide (nth i' ms 0) M').
      { unfold M'. apply nth_divides_prod. exact Hi'. }
      assert (Hmod : c mod (nth i' ms 0) = c' mod (nth i' ms 0)).
      {
        apply mod_divides_transfer with (M := M').
        - apply Hpos_tail. exact Hi'.
        - exact HMpos.
        - exact Hdiv.
        - exact HcM.
      }
      rewrite Hmod.
      apply Hc'. exact Hi'.
Qed.

Lemma nth_map_beta_mod_seq :
  forall a i,
    i < length a ->
    nth i (map (beta_mod a) (seq 0 (length a))) 0 = beta_mod a i.
Proof.
  intros a i Hi.
  rewrite (nth_default_irrel _ _ i 0 (beta_mod a 0)).
  2:{ rewrite length_map, length_seq. exact Hi. }
  rewrite map_nth.
  rewrite seq_nth by exact Hi.
  rewrite Nat.add_0_l.
  reflexivity.
Qed.

Theorem beta_exists :
  forall (a : list nat),
    exists c, forall i,
      i < length a ->
      beta c (beta_d a) i = nth i a 0.
Proof.
  intro a.
  set (ms := map (beta_mod a) (seq 0 (length a))).
  assert (Hlen : length ms = length a).
  {
    unfold ms. rewrite length_map, length_seq. reflexivity.
  }
  assert (Hpos : forall i, i < length ms -> nth i ms 0 > 0).
  {
    intros i Hi.
    unfold ms in *.
    assert (Hi' : i < length a).
    { rewrite <- Hlen. exact Hi. }
    rewrite nth_map_beta_mod_seq; [|exact Hi'].
    unfold beta_mod, modulus.
    lia.
  }
  assert (Hpair :
    forall i j, i < length ms -> j < length ms -> i <> j ->
      Nat.gcd (nth i ms 0) (nth j ms 0) = 1).
  {
    intros i j Hi Hj Hij.
    unfold ms in *.
    assert (Hi' : i < length a) by (rewrite <- Hlen; exact Hi).
    assert (Hj' : j < length a) by (rewrite <- Hlen; exact Hj).
    repeat rewrite nth_map_beta_mod_seq by assumption.
    apply beta_mod_coprime; assumption.
  }
  destruct (crt_list ms a Hlen Hpos Hpair) as [c Hc].
  exists c.
  intros i Hi.
  unfold beta.
  unfold ms in Hc.
  specialize (Hc i (ltac:(rewrite length_map, length_seq; exact Hi))).
  rewrite nth_map_beta_mod_seq in Hc by exact Hi.
  unfold beta_mod, modulus in Hc.
  rewrite Hc.
  apply Nat.mod_small.
  apply beta_mod_gt_value.
  exact Hi.
Qed.