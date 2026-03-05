(* R00__Odd_Part.v *)

From Coq Require Import Arith Bool Lia List PeanoNat.
Import ListNotations.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Pigeonhole Divisibility — Odd-Part Decomposition         *)
(*                                                                       *)
(*  We define the odd-part map and establish the properties needed by    *)
(*  the divisibility theorem in R01.  Every positive integer a admits    *)
(*  a unique decomposition a = 2^k m with m odd; we call m the odd       *)
(*  part of a.  The key facts are:                                       *)
(*                                                                       *)
(*    (i)   odd_part a is always odd                                     *)
(*    (ii)  odd_part a divides a                                         *)
(*    (iii) odd_part a <= a                                              *)
(*    (iv)  same odd part implies divisibility                           *)
(*    (v)   there are exactly n odd numbers in {1, ..., 2n}              *)
(*                                                                       *)
(*************************************************************************)

Section Odd_Part_Definitions.

(*
  We strip all factors of 2 from a positive natural number.
  The fuel parameter bounds the recursion; n itself suffices
  since div2 strictly decreases positive values.
*)

Fixpoint odd_part_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
      if Nat.even n
      then odd_part_aux fuel' (Nat.div2 n)
      else n
  end.

(*
  The odd part of n.
*)

Definition odd_part (n : nat) : nat :=
  odd_part_aux n n.

(*
  The 2-adic valuation: the exponent k in a = 2^k odd_part(a).
*)

Fixpoint val2_aux (fuel n : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      if Nat.even n
      then S (val2_aux fuel' (Nat.div2 n))
      else 0
  end.

(*
  The 2-adic valuation of n.
*)

Definition val2 (n : nat) : nat :=
  val2_aux n n.

End Odd_Part_Definitions.

Section Odd_Part_Properties.

(*
  The odd_part_aux result is bounded by n.
*)

Lemma odd_part_aux_le :
  forall fuel n,
    odd_part_aux fuel n <= n.
Proof.
  induction fuel as [|fuel IH]; intros n.
  - simpl. lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + specialize (IH (Nat.div2 n)).
      assert (Hdiv2 : Nat.div2 n <= n).
      { apply (Nat.div2_decr n n). lia. }
      lia.
    + lia.
Qed.

(*
  The result of odd_part_aux is odd, provided n >= 1.
*)

Lemma odd_part_aux_odd :
  forall fuel n,
    1 <= n ->
    n <= fuel ->
    Nat.odd (odd_part_aux fuel n) = true.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hle.
  - lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + assert (Hn_div2 : 1 <= Nat.div2 n).
      { apply Nat.even_spec in Heven.
        destruct Heven as [k Hk].
        subst n.
        rewrite Nat.div2_double.
        destruct k as [|k']; lia. }
      assert (Hle_div2 : Nat.div2 n <= fuel).
      { pose proof (Nat.lt_div2 n Hn) as Hlt. lia. }
      exact (IH (Nat.div2 n) Hn_div2 Hle_div2).
    + rewrite <- Nat.negb_even.
      rewrite Heven.
      reflexivity.
Qed.

(*
  The odd part of n is odd.
*)

Lemma odd_part_odd :
  forall n,
    1 <= n ->
    Nat.odd (odd_part n) = true.
Proof.
  intros n Hn.
  unfold odd_part.
  apply odd_part_aux_odd.
  - exact Hn.
  - lia.
Qed.

(*
  The odd part of n is at most n.
*)

Lemma odd_part_le :
  forall n, odd_part n <= n.
Proof.
  intro n.
  unfold odd_part.
  apply odd_part_aux_le.
Qed.

(*
  The odd part of n is at least 1 when n >= 1.
*)

Lemma odd_part_pos :
  forall n,
    1 <= n ->
    1 <= odd_part n.
Proof.
  intros n Hn.
  pose proof (odd_part_odd n Hn) as Hodd.
  destruct (odd_part n) as [|m].
  - simpl in Hodd. discriminate.
  - lia.
Qed.

(*
  The odd_part_aux result divides n.
*)

Lemma odd_part_aux_divides :
  forall fuel n,
    1 <= n ->
    n <= fuel ->
    Nat.divide (odd_part_aux fuel n) n.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hle.
  - lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + assert (Hd : n = 2 * Nat.div2 n).
      { apply Nat.even_spec in Heven.
        destruct Heven as [k Hk].
        rewrite Hk.
        rewrite Nat.div2_double.
        lia. }
      assert (Hdiv2_pos : 1 <= Nat.div2 n).
      { apply Nat.even_spec in Heven.
        destruct Heven as [k Hk].
        subst n.
        rewrite Nat.div2_double.
        destruct k as [|k']; lia. }
      assert (Hdiv2_le : Nat.div2 n <= fuel).
      { pose proof (Nat.lt_div2 n Hn) as Hlt. lia. }
      specialize (IH (Nat.div2 n) Hdiv2_pos Hdiv2_le).
      destruct IH as [q Hq].
      exists (2 * q).
      lia.
    + exists 1. lia.
Qed.

(*
  The odd part of n divides n.
*)

Lemma odd_part_divides :
  forall n,
    1 <= n ->
    Nat.divide (odd_part n) n.
Proof.
  intros n Hn.
  unfold odd_part.
  apply odd_part_aux_divides.
  - exact Hn.
  - lia.
Qed.

(*
  Fuel-indexed decomposition: n = 2^(val2_aux fuel n) * odd_part_aux fuel n.
*)

Lemma decomposition_aux :
  forall fuel n,
    1 <= n ->
    n <= fuel ->
    n = 2 ^ (val2_aux fuel n) * odd_part_aux fuel n.
Proof.
  induction fuel as [|fuel IH]; intros n Hn Hle.
  - lia.
  - simpl.
    destruct (Nat.even n) eqn:Heven.
    + assert (Hd : n = 2 * Nat.div2 n).
      { apply Nat.even_spec in Heven.
        destruct Heven as [k Hk].
        rewrite Hk.
        rewrite Nat.div2_double.
        lia. }
      assert (Hdiv2_pos : 1 <= Nat.div2 n).
      { apply Nat.even_spec in Heven.
        destruct Heven as [k Hk].
        subst n.
        rewrite Nat.div2_double.
        destruct k as [|k']; lia. }
      assert (Hdiv2_le : Nat.div2 n <= fuel).
      { pose proof (Nat.lt_div2 n Hn) as Hlt. lia. }
      specialize (IH (Nat.div2 n) Hdiv2_pos Hdiv2_le).
      rewrite Hd at 1.
      rewrite IH at 1.
      rewrite Nat.pow_succ_r'.
      rewrite <- Nat.mul_assoc.
      reflexivity.
    + simpl.
      lia.
Qed.

(*
  The quotient n / odd_part(n) is a power of 2.  We express this as:
  n = 2^(val2 n) times odd_part(n).
*)

Lemma decomposition :
  forall n,
    1 <= n ->
    n = 2 ^ (val2 n) * odd_part n.
Proof.
  intros n Hn.
  unfold val2, odd_part.
  apply decomposition_aux.
  - exact Hn.
  - lia.
Qed.

(*
  If two positive integers share the same odd part, one divides the
  other.  This follows because a = 2^k m and b = 2^l m, so
  assuming k <= l we get b = 2^(l-k) a.
*)

Theorem same_odd_part_divides :
  forall a b,
    1 <= a ->
    1 <= b ->
    odd_part a = odd_part b ->
    Nat.divide a b \/ Nat.divide b a.
Proof.
  intros a b Ha Hb Heq.
  destruct (Nat.le_gt_cases (val2 a) (val2 b)) as [Hab | Hba].
  - left.
    exists (2 ^ (val2 b - val2 a)).
    replace b with (2 ^ val2 b * odd_part b) at 1.
    2:{ symmetry. apply decomposition. exact Hb. }
    replace a with (2 ^ val2 a * odd_part a) at 2.
    2:{ symmetry. apply decomposition. exact Ha. }
    rewrite <- Heq.
    assert (Hexp : val2 b = (val2 b - val2 a) + val2 a) by lia.
    rewrite Hexp at 1.
    rewrite Nat.pow_add_r.
    rewrite <- Nat.mul_assoc.
    reflexivity.
  - right.
    exists (2 ^ (val2 a - val2 b)).
    replace a with (2 ^ val2 a * odd_part a) at 1.
    2:{ symmetry. apply decomposition. exact Ha. }
    replace b with (2 ^ val2 b * odd_part b) at 2.
    2:{ symmetry. apply decomposition. exact Hb. }
    rewrite Heq.
    assert (Hle : val2 b <= val2 a) by lia.
    assert (Hexp : val2 a = (val2 a - val2 b) + val2 b) by lia.
    rewrite Hexp at 1.
    rewrite Nat.pow_add_r.
    rewrite <- Nat.mul_assoc.
    reflexivity.
Qed.

End Odd_Part_Properties.

Section Odd_Range.

(*
  We generate the list of odd numbers in {1, ..., 2n}.
  This list has exactly n elements and serves as the set of
  pigeonholes in the main theorem.
*)

Fixpoint odd_range (n : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => odd_range n' ++ [2 * n' + 1]
  end.

(*
  The odd_range has exactly n elements.
*)

Lemma odd_range_length :
  forall n, length (odd_range n) = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl.
    rewrite length_app. simpl.
    rewrite IH. lia.
Qed.

(*
  Characterization of membership in odd_range: k is in the list
  iff k = 2i + 1 for some i < n.
*)

Lemma odd_range_in_iff :
  forall n k,
    In k (odd_range n) <-> exists i, i < n /\ k = 2 * i + 1.
Proof.
  induction n as [|n IH]; intros k.
  - simpl. split.
    + intros Hin. inversion Hin.
    + intros [i [Hi _]]. lia.
  - simpl. rewrite in_app_iff. split.
    + intros [Hin | Hin].
      * apply IH in Hin.
        destruct Hin as [i [Hi Hk]].
        exists i. split; lia.
      * simpl in Hin.
        destruct Hin as [Hk | Hfalse].
        { subst k. exists n. split; lia. }
        { contradiction. }
    + intros [i [Hi Hk]].
      assert (i < n \/ i = n) as [Hil | Hieq] by lia.
      * left. apply IH. exists i. split; lia.
      * right. subst i. simpl. left. symmetry. exact Hk.
Qed.

(*
  Every element of odd_range n is odd.
*)

Lemma odd_range_all_odd :
  forall n k,
    In k (odd_range n) ->
    Nat.odd k = true.
Proof.
  intros n k Hin.
  apply odd_range_in_iff in Hin.
  destruct Hin as [i [_ Hk]].
  subst k.
  apply Nat.odd_spec.
  exists i.
  lia.
Qed.

(*
  Every element of odd_range n is between 1 and 2n - 1.
*)

Lemma odd_range_bounds :
  forall n k,
    In k (odd_range n) ->
    1 <= k /\ k <= 2 * n - 1.
Proof.
  induction n as [|n IH]; intros k Hin.
  - inversion Hin.
  - simpl in Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + destruct (IH k Hin). split; lia.
    + simpl in Hin.
      destruct Hin as [Heq | Hfalse]; [| contradiction].
      subst k. lia.
Qed.

(*
  The odd_range has no duplicate entries.
*)

Lemma odd_range_NoDup :
  forall n, NoDup (odd_range n).
Proof.
  induction n as [|n IH].
  - constructor.
  - simpl.
    apply NoDup_app.
    + exact IH.
    + constructor.
      * intro H. inversion H.
      * constructor.
    + intros x Hin1 Hin2.
      simpl in Hin2.
      destruct Hin2 as [Heq | Hfalse]; [| contradiction].
      subst x.
      apply odd_range_bounds in Hin1. lia.
Qed.

(*
  The odd part of any a in {1, ..., 2n} belongs to odd_range n.
  This is the counting fact that gives us only n pigeonholes.
*)

Lemma odd_part_in_range :
  forall n a,
    1 <= a ->
    a <= 2 * n ->
    In (odd_part a) (odd_range n).
Proof.
  intros n a Ha_pos Ha_bound.
  apply odd_range_in_iff.
  assert (Hodd : Nat.odd (odd_part a) = true).
  { apply odd_part_odd. exact Ha_pos. }
  assert (Hpos : 1 <= odd_part a).
  { apply odd_part_pos. exact Ha_pos. }
  assert (Hle : odd_part a <= 2 * n).
  { eapply Nat.le_trans.
    - apply odd_part_le.
    - exact Ha_bound. }
  apply Nat.odd_spec in Hodd.
  destruct Hodd as [i Hi].
  exists i.
  split.
  - rewrite Hi in Hle. lia.
  - exact Hi.
Qed.

End Odd_Range.
