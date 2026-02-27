(* R02__Zeckendorf.v *)

From Coq Require Import Arith List Bool PeanoNat Lia.
Import ListNotations.
From T002 Require Import R01__Foundation_Fibonacci.

(*************************************************************************)
(*                                                                       *)
(*  Zeckendorf Support Lists — Definitions                               *)
(*                                                                       *)
(*************************************************************************)

Fixpoint strictly_decreasing (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: xs'' => a > b /\ strictly_decreasing xs'
      end
  end.

Fixpoint no_adjacent (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' =>
      match xs' with
      | [] => True
      | b :: xs'' => a >= b + 2 /\ no_adjacent xs'
      end
  end.

Fixpoint all_ge_2 (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | a :: xs' => 2 <= a /\ all_ge_2 xs'
  end.

Definition zeck_valid (xs : list nat) : Prop :=
  strictly_decreasing xs /\ no_adjacent xs /\ all_ge_2 xs.

(*************************************************************************)
(*                                                                       *)
(*  Greedy Support Constructor                                           *)
(*                                                                       *)
(*************************************************************************)

Fixpoint find_r_aux (x k fuel : nat) : nat :=
  match fuel with
  | 0 => k
  | S fuel' =>
      if Nat.ltb x (F k)
      then k
      else find_r_aux x (S k) fuel'
  end.

Definition r0 (x : nat) : nat := find_r_aux x 0 (S (S x)).

Fixpoint zeck_greedy_down (k rem : nat) (prev_taken : bool)
  : list nat * nat :=
  match k with
  | 0 => ([], rem)
  | S k' =>
      match k' with
      | 0 => ([], rem)

      (*
         exclude index 1 for canonicality
      *)

      | S k'' =>
          if prev_taken then
            zeck_greedy_down k' rem false
          else
            if Nat.leb (F k) rem then
              let pr := zeck_greedy_down k' (rem - F k) true in
              (k :: fst pr, snd pr)
            else
              zeck_greedy_down k' rem false
      end
  end.

Definition Z0 (x : nat) : list nat :=
  fst (zeck_greedy_down (r0 x) x false).

Definition P0 : Params :=
  {| Z := Z0; r := r0 |}.




(*
   R02__Uniqueness.v
*)
(*
   T002 / C002__Zeckendorf
*)

From Coq Require Import Arith PeanoNat Lia List.
Import ListNotations.
From T002 Require Import R01__Foundation_Fibonacci.

(*************************************************************************)
(*                                                                       *)
(*  Fibonacci Infrastructure                                             *)
(*                                                                       *)
(*************************************************************************)

Lemma fib_pair_S : forall n a b,
  fib_pair n = (a, b) -> fib_pair (S n) = (b, a + b).
Proof.
  intros n a b H.
  simpl. rewrite H. reflexivity.
Qed.

Lemma F_S : forall n, F (S n) = snd (fib_pair n).
Proof.
  intro n. unfold F. simpl. destruct (fib_pair n) as [a b]. reflexivity.
Qed.

Lemma F_step : forall n, F (S (S n)) = F (S n) + F n.
Proof.
  intro n.
  rewrite F_S.
  destruct (fib_pair n) as [a b] eqn:Hn.
  assert (Hs : fib_pair (S n) = (b, a + b)).
  { simpl. rewrite Hn. reflexivity. }
  rewrite Hs.
  unfold F. rewrite Hs. rewrite Hn. simpl.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma F_S_ge : forall n, F (S n) >= F n.
Proof.
  induction n as [|n IH].
  - unfold F. simpl. lia.
  - rewrite F_step. lia.
Qed.

Lemma F_pos_S : forall n, F (S n) >= 1.
Proof.
  induction n as [|n IH].
  - unfold F. simpl. lia.
  - rewrite F_step. lia.
Qed.

Lemma F_pos : forall n, n >= 1 -> F n >= 1.
Proof.
  intros n H.
  destruct n as [|n].
  - lia.
  - apply F_pos_S.
Qed.

Lemma F_monotone_le : forall a b, a < b -> F a <= F b.
Proof.
  intros a b Hlt.
  induction b as [|b IH]; [lia|].
  destruct (Nat.eq_dec a b) as [Heq|Hne].
  - subst. apply F_S_ge.
  - assert (a < b) by lia.
    specialize (IH H).
    apply Nat.le_trans with (m:=F b); [exact IH |].
    apply F_S_ge.
Qed.

Lemma F_gap2_gt : forall a, F a < F (S (S a)).
Proof.
  intro a.
  rewrite F_step.
  assert (Hpos : F (S a) >= 1) by apply F_pos_S.
  lia.
Qed.

Lemma F_monotone_gap2 : forall a b, a + 1 < b -> F a < F b.
Proof.
  intros a b Hlt.
  assert (Hle : S (S a) <= b) by lia.
  apply Nat.lt_le_trans with (m:=F (S (S a))).
  - apply F_gap2_gt.
  - destruct (Nat.eq_dec (S (S a)) b) as [Heq|Hne].
    + subst. apply Nat.le_refl.
    + apply F_monotone_le. lia.
Qed.

Lemma add_sub_cancel_r : forall a b, a <= b -> a + (b - a) = b.
Proof.
  intros a b Hle. lia.
Qed.

Lemma add_assoc_l : forall a b c, a + b + c = a + (b + c).
Proof.
  intros a b c. lia.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Search Properties for r0                                             *)
(*                                                                       *)
(*************************************************************************)

Lemma F_ge_Sn : forall n, F (S (S n)) >= S n.
Proof.
  induction n as [|n IH].
  - vm_compute. lia.
  - rewrite F_step.
    assert (Hpos : F (S n) >= 1) by apply F_pos_S.
    lia.
Qed.

Lemma find_r_aux_upper_from_witness :
  forall x k fuel,
    x < F (k + fuel) ->
    x < F (find_r_aux x k fuel).
Proof.
  intros x k fuel.
  revert k.
  induction fuel as [|fuel IH]; intros k Hlt.
  - simpl in *. replace (k + 0) with k in Hlt by lia. simpl. exact Hlt.
  - simpl in *.
    destruct (Nat.ltb x (F k)) eqn:Hk.
    + apply Nat.ltb_lt. exact Hk.
    + apply IH.
      replace (S k + fuel) with (k + S fuel) by lia.
      exact Hlt.
Qed.

Lemma find_r_aux_before_false :
  forall x k fuel j,
    k <= j ->
    j < find_r_aux x k fuel ->
    Nat.ltb x (F j) = false.
Proof.
  intros x k fuel.
  revert x k.
  induction fuel as [|fuel IH]; intros x k j Hkj Hlt.
  - simpl in Hlt. lia.
  - simpl in Hlt.
    destruct (Nat.ltb x (F k)) eqn:Hk.
    + lia.
    + destruct (Nat.eq_dec j k) as [->|Hneq].
      * exact Hk.
      * assert (Hskj : S k <= j) by lia.
        eapply IH; eauto.
Qed.

Lemma r0_upper :
  forall n, n < F (r0 n).
Proof.
  intro n.
  unfold r0.
  apply find_r_aux_upper_from_witness.
  replace (0 + S (S n)) with (S (S n)) by lia.
  assert (Hge : F (S (S n)) >= S n) by apply F_ge_Sn.
  lia.
Qed.

Corollary r0_upper_S :
  forall n, n < F (S (r0 n)).
Proof.
  intro n.
  assert (Hup : n < F (r0 n)) by apply r0_upper.
  assert (Hmono : F (r0 n) <= F (S (r0 n))) by apply F_S_ge.
  lia.
Qed.

Lemma r0_minimal :
  forall n k, k < r0 n -> F k <= n.
Proof.
  intros n k Hlt.
  unfold r0 in Hlt.
  pose proof (find_r_aux_before_false n 0 (S (S n)) k (Nat.le_0_l k) Hlt) as Hfalse.
  apply Nat.ltb_ge in Hfalse.
  exact Hfalse.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Greedy Invariant — Structural Components                             *)
(*                                                                       *)
(*************************************************************************)

Fixpoint all_le (m : nat) (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' => x <= m /\ all_le m xs'
  end.

Definition bound (k : nat) (prev_taken : bool) : nat :=
  if prev_taken then Nat.pred k else k.

Lemma all_le_weaken : forall m n xs,
  all_le m xs -> m <= n -> all_le n xs.
Proof.
  induction xs as [|x xs IH]; intros Hle Hmn; simpl in *; auto.
  destruct Hle as [Hx Hxs].
  split; [lia | exact (IH Hxs Hmn)].
Qed.

Lemma zeck_valid_cons_ge2 :
  forall m xs,
    zeck_valid xs ->
    all_le m xs ->
    zeck_valid (S (S m) :: xs).
Proof.
  intros m xs [Hdec [Hadj Hge]] Hall.
  split; [|split].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hdec].
  - destruct xs as [|x xs']; simpl; auto.
    destruct Hall as [Hx Hall'].
    split; [lia | exact Hadj].
  - simpl. split; [lia | exact Hge].
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Greedy Invariant                                                     *)
(*                                                                       *)
(*************************************************************************)

Definition greedy_inv k rem prev_taken xs rem' :=
  sumF xs + rem' = rem /\
  zeck_valid xs /\
  all_le (bound k prev_taken) xs /\
  (k <= 1 -> xs = [] /\ rem' = rem) /\
  (rem < F (S (bound k prev_taken)) -> rem' < F (S (bound k prev_taken))).

Lemma greedy_take_step_sum :
  forall k rem xs rem',
    F k <= rem ->
    sumF xs + rem' = rem - F k ->
    sumF (k :: xs) + rem' = rem.
Proof.
  intros k rem xs rem' Hle Hsum.
  simpl.
  rewrite <- Nat.add_assoc.
  rewrite Hsum.
  apply add_sub_cancel_r.
  exact Hle.
Qed.

Lemma zeck_greedy_down_correct_core :
  forall k rem prev_taken xs rem',
    zeck_greedy_down k rem prev_taken = (xs, rem') ->
    greedy_inv k rem prev_taken xs rem'.
Proof.
  induction k as [|k IH]; intros rem prev xs rem' H.
  - simpl in H. inversion H; subst.
    assert (Hsum : sumF [] + rem' = rem') by (simpl; lia).
    assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
    assert (Hall : all_le (bound 0 prev) []) by (simpl; exact I).
    assert (Hlow : 0 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
      by (intros _; split; reflexivity).
    assert (Hbd : rem' < F (S (bound 0 prev)) -> rem' < F (S (bound 0 prev)))
      by (intro Hrem; exact Hrem).
    exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
  - destruct k as [|k']; simpl in H.
    + inversion H; subst.
      assert (Hsum : sumF [] + rem' = rem') by (simpl; lia).
      assert (Hz : zeck_valid []) by (simpl; split; [exact I|]; split; exact I).
      assert (Hall : all_le (bound 1 prev) []) by (simpl; exact I).
      assert (Hlow : 1 <= 1 -> ([] : list nat) = [] /\ rem' = rem')
        by (intros _; split; reflexivity).
      assert (Hbd : rem' < F (S (bound 1 prev)) -> rem' < F (S (bound 1 prev)))
        by (intro Hrem; exact Hrem).
      exact (conj Hsum (conj Hz (conj Hall (conj Hlow Hbd)))).
    + destruct prev eqn:Hprev.

      (*
         prev_taken = true: skip this index
      *)

      * specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
        refine (conj Hsum (conj Hz (conj _ (conj _ _))));
          [simpl; exact Hall | intros Hk; lia | intros Hrem; lia].

        (*
           prev_taken = false: decide to take or skip
        *)

      * destruct (Nat.leb (F (S (S k'))) rem) eqn:Hle.
        -- (*
              take k
            *)
           destruct (zeck_greedy_down (S k') (rem - F (S (S k'))) true)
             as [xs' rem''] eqn:Hpr.
           change
             ((S (S k')
               :: fst (zeck_greedy_down (S k') (rem - F (S (S k'))) true),
               snd (zeck_greedy_down (S k') (rem - F (S (S k'))) true))
              = (xs, rem')) in H.
           rewrite Hpr in H.
           inversion H; subst xs rem'. clear H.
           specialize (IH (rem - F (S (S k'))) true xs' rem'' Hpr)
             as [Hsum [Hz [Hall [Hlow Hbd]]]].
           refine (conj _ (conj _ (conj _ (conj _ _))));
             [ apply Nat.leb_le in Hle;
               eapply greedy_take_step_sum; [exact Hle | exact Hsum]
             | simpl in Hall; apply (zeck_valid_cons_ge2 k' xs'); assumption

             (*
                zeck_valid for cons
             *)

             | simpl; split; [lia|]; apply all_le_weaken with (m:=k'); [exact Hall| lia]

             (*
                all_le bound k false
             *)

             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_le in Hle;
               simpl in Hrem;
               assert (Hinner : rem - F (S (S k')) < F (S k')) by
                 (rewrite F_step in Hrem; lia);
               assert (Hrem'' : rem'' < F (S k')) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=F (S k')); [exact Hrem''|];
               simpl; apply F_monotone_le; lia ].
        -- specialize (IH rem false xs rem' H) as [Hsum [Hz [Hall [Hlow Hbd]]]].
        
            (*
               skip k
            *)

           refine (conj Hsum (conj Hz (conj _ (conj _ _))));
             [ simpl; apply all_le_weaken with (m:=S k'); [exact Hall| lia]
             | intros Hk; lia
             | intros Hrem;
               apply Nat.leb_gt in Hle;
               assert (Hinner : rem < F (S (S k'))) by lia;
               assert (Hrem' : rem' < F (S (S k'))) by (apply Hbd; exact Hinner);
               apply Nat.lt_le_trans with (m:=F (S (S k'))); [exact Hrem'|];
               simpl; apply F_monotone_le; lia ].
Qed.

Lemma zeck_greedy_down_inv_k0 :
  forall rem prev,
    greedy_inv 0 rem prev
      (fst (zeck_greedy_down 0 rem prev))
      (snd (zeck_greedy_down 0 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_k1 :
  forall rem prev,
    greedy_inv 1 rem prev
      (fst (zeck_greedy_down 1 rem prev))
      (snd (zeck_greedy_down 1 rem prev)).
Proof.
  intros rem prev.
  apply zeck_greedy_down_correct_core.
  reflexivity.
Qed.

Lemma zeck_greedy_down_inv_skip_prev :
  forall k rem xs rem',
    zeck_greedy_down (S (S k)) rem true = (xs, rem') ->
    greedy_inv (S (S k)) rem true xs rem'.
Proof.
  intros k rem xs rem' H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_skip_lt :
  forall k rem xs rem',
    F (S (S k)) > rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Lemma zeck_greedy_down_inv_take :
  forall k rem xs rem',
    F (S (S k)) <= rem ->
    zeck_greedy_down (S (S k)) rem false = (xs, rem') ->
    greedy_inv (S (S k)) rem false xs rem'.
Proof.
  intros k rem xs rem' _ H.
  apply zeck_greedy_down_correct_core.
  exact H.
Qed.

Theorem zeck_greedy_down_correct :
  forall k rem prev xs rem',
    zeck_greedy_down k rem prev = (xs, rem') ->
    greedy_inv k rem prev xs rem'.
Proof.
  intros k rem prev xs rem' H.
  destruct k as [|k'].
  - apply zeck_greedy_down_correct_core. exact H.
  - destruct k' as [|k''].
    + apply zeck_greedy_down_correct_core. exact H.
    + destruct prev.
      * apply zeck_greedy_down_inv_skip_prev. exact H.
      * destruct (Nat.leb (F (S (S k''))) rem) eqn:Hleb.
        -- apply zeck_greedy_down_inv_take.
           ++ apply Nat.leb_le. exact Hleb.
           ++ exact H.
        -- apply zeck_greedy_down_inv_skip_lt.
           ++ apply Nat.leb_gt. exact Hleb.
           ++ exact H.
Qed.

Lemma greedy_top_bound :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < F (S (r0 n)).
Proof.
  intros n xs rem' H.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' H)
    as [_ [_ [_ [_ Hbd]]]].
  simpl in Hbd.
  apply Hbd.
  apply r0_upper_S.
Qed.

Lemma sumF_prefix_lt_next :
  forall k rem xs rem',
    greedy_inv (S (S k)) rem false (S (S k) :: xs) rem' ->
    rem < F (S (S (S k))) ->
    sumF (S (S k) :: xs) < F (S (S (S k))).
Proof.
  intros k rem xs rem' Hinv Hrem.
  destruct Hinv as [Hsum [_ [_ [_ _]]]].
  assert (sumF (S (S k) :: xs) <= rem) by lia.
  lia.
Qed.

Lemma rem_lt_1_is_0 : forall r, r < 1 -> r = 0.
Proof.
  intros r Hr. lia.
Qed.

Lemma bound_k1_le_1 : forall prev, bound 1 prev <= 1.
Proof.
  intro prev. destruct prev; simpl; lia.
Qed.

Lemma F_2_eq_1 : F 2 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma F_1_eq_1 : F 1 = 1.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma rem_lt_1_from_inv_k1 :
  forall rem prev xs rem',
    zeck_greedy_down 1 rem prev = (xs, rem') ->
    greedy_inv 1 rem prev xs rem' ->
    rem < F (S (bound 1 prev)) ->
    rem' < 1.
Proof.
  intros rem prev xs rem' Hcall Hinv Hpre.
  destruct Hinv as [_ [_ [_ [_ Hbd]]]].
  specialize (Hbd Hpre).
  destruct prev.
  - simpl in Hbd. rewrite F_1_eq_1 in Hbd. lia.
  - simpl in Hbd. rewrite F_2_eq_1 in Hbd. lia.
Qed.

Lemma greedy_rem_lt_1_false :
  forall k rem xs rem',
    rem < F (S k) ->
    zeck_greedy_down k rem false = (xs, rem') ->
    rem' < 1.
Proof.
  refine (well_founded_induction
            lt_wf
            (fun k =>
               forall rem xs rem',
                 rem < F (S k) ->
                 zeck_greedy_down k rem false = (xs, rem') ->
                 rem' < 1) _).
  intros k IH rem xs rem' Hbound Hcall.
  destruct k as [|k1].
  - simpl in Hcall. inversion Hcall; subst. exact Hbound.
  - destruct k1 as [|k2].
    + simpl in Hcall. inversion Hcall; subst.
      rewrite F_2_eq_1 in Hbound. exact Hbound.
    + simpl in Hcall.
      destruct (Nat.leb (F (S (S k2))) rem) eqn:Hle.
      * destruct (zeck_greedy_down (S k2) (rem - F (S (S k2))) true)
          as [xs1 rem1] eqn:Hrec.
        change
          ((S (S k2)
            :: fst (zeck_greedy_down (S k2) (rem - F (S (S k2))) true),
            snd (zeck_greedy_down (S k2) (rem - F (S (S k2))) true))
           = (xs, rem')) in Hcall.
        rewrite Hrec in Hcall.
        inversion Hcall; subst xs rem'. clear Hcall.
        apply Nat.leb_le in Hle.
        assert (Hrem1 : rem - F (S (S k2)) < F (S k2)).
        { rewrite F_step in Hbound. lia. }
        destruct k2 as [|k3].
        -- simpl in Hrec. inversion Hrec; subst.
           rewrite F_1_eq_1 in Hrem1. exact Hrem1.
        -- simpl in Hrec.
           pose proof (IH (S k3) ltac:(lia)) as IHk.
           exact (IHk (rem - F (S (S (S k3)))) xs1 rem1 Hrem1 Hrec).
      * apply Nat.leb_gt in Hle.
        pose proof (IH (S k2) ltac:(lia)) as IHk.
        exact (IHk rem xs rem' Hle Hcall).
Qed.

Lemma Z0_rem_lt_1 :
  forall n xs rem',
    zeck_greedy_down (r0 n) n false = (xs, rem') ->
    rem' < 1.
Proof.
  intros n xs rem' H.
  eapply greedy_rem_lt_1_false; eauto.
  apply r0_upper_S.
Qed.

Theorem Z0_sound : forall n, sumF (Z0 n) = n.
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [Hsum _].
  assert (Hrem1 : rem' < 1) by (eapply Z0_rem_lt_1; exact Hgd).
  assert (Hrem0 : rem' = 0) by (apply rem_lt_1_is_0; exact Hrem1).
  rewrite Hrem0 in Hsum.
  rewrite Nat.add_0_r in Hsum.
  exact Hsum.
Qed.

Theorem Z0_valid : forall n, zeck_valid (Z0 n).
Proof.
  intro n.
  unfold Z0.
  destruct (zeck_greedy_down (r0 n) n false) as [xs rem'] eqn:Hgd.
  pose proof (zeck_greedy_down_correct (r0 n) n false xs rem' Hgd)
    as [_ [Hvalid _]].
  exact Hvalid.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Canonical Inversion: Basic Bounds                                    *)
(*                                                                       *)
(*************************************************************************)

Lemma sumF_ge_head :
  forall k xs, sumF (k :: xs) >= F k.
Proof.
  intros k xs. simpl. lia.
Qed.

Lemma zeck_valid_tail :
  forall k xs,
    zeck_valid (k :: xs) ->
    zeck_valid xs.
Proof.
  intros k xs [Hdec [Hadj Hge]].
  destruct xs as [|a xs'].
  - simpl. split; [trivial|]. split; trivial.
  - simpl in Hdec, Hadj, Hge.
    destruct Hdec as [_ Hdec'].
    destruct Hadj as [_ Hadj'].
    destruct Hge as [_ Hge'].
    split; [exact Hdec'|]. split; assumption.
Qed.

Lemma zeck_valid_head_ge_2 :
  forall k xs,
    zeck_valid (k :: xs) ->
    2 <= k.
Proof.
  intros k xs [_ [_ Hge]].
  simpl in Hge.
  tauto.
Qed.

Lemma F_le_of_le : forall a b, a <= b -> F a <= F b.
Proof.
  intros a b Hle.
  destruct (Nat.eq_dec a b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply F_monotone_le. lia.
Qed.

Lemma F_lt_succ_of_ge2 : forall k, 2 <= k -> F k < F (S k).
Proof.
  intros k Hk.
  destruct k as [|[|k']]; try lia.
  replace (F (S (S (S k')))) with (F (S (S k')) + F (S k')) by
      (symmetry; apply F_step).
  assert (Hpos : F (S k') >= 1) by apply F_pos_S.
  lia.
Qed.

Lemma F_step_pred : forall k, 1 <= k -> F (S k) = F k + F (Nat.pred k).
Proof.
  intros k Hk.
  destruct k as [|k']; [lia|].
  destruct k' as [|k''].
  - vm_compute. reflexivity.
  - simpl. apply F_step.
Qed.

Lemma sumF_lt_next_of_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    sumF (k :: xs) < F (S k).
Proof.
  intros k xs Hvalid.
  revert k Hvalid.
  induction xs as [|x xs' IH]; intros k Hvalid; simpl.
  - apply zeck_valid_head_ge_2 in Hvalid.
    rewrite Nat.add_0_r.
    apply F_lt_succ_of_ge2.
    exact Hvalid.
  - pose proof (zeck_valid_tail k (x :: xs') Hvalid) as Htail_valid.
    pose proof (IH x Htail_valid) as Htail.
    destruct Hvalid as [_ [Hadj _]].
    simpl in Hadj.
    destruct Hadj as [Hgap _].
    assert (Hsx : S x <= Nat.pred k) by lia.
    assert (Hsx_le : F (S x) <= F (Nat.pred k)).
    { apply F_le_of_le. exact Hsx. }
    assert (Hk1 : 1 <= k) by lia.
    assert (Hstep : F (S k) = F k + F (Nat.pred k)).
    { apply F_step_pred. exact Hk1. }
    rewrite Hstep.
    assert (Hlt_pred : F x + sumF xs' < F (Nat.pred k)).
    { eapply Nat.lt_le_trans; [exact Htail | exact Hsx_le]. }
    lia.
Qed.

Lemma sumF_cons_pos_valid :
  forall k xs,
    zeck_valid (k :: xs) ->
    0 < sumF (k :: xs).
Proof.
  intros k xs Hvalid.
  simpl.
  assert (Hk2 : 2 <= k) by (apply zeck_valid_head_ge_2 with (xs:=xs); exact Hvalid).
  assert (Hf : F k >= 1) by (apply F_pos; lia).
  lia.
Qed.

Lemma F_succ_le_of_lt_ge2 :
  forall a b,
    2 <= a ->
    a < b ->
    F (S a) <= F b.
Proof.
  intros a b Ha Hlt.
  destruct (Nat.eq_dec (S a) b) as [Heq|Hneq].
  - subst. apply Nat.le_refl.
  - apply F_monotone_le. lia.
Qed.

Lemma Zeckendorf_unique_core :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sumF xs = sumF ys ->
    xs = ys.
Proof.
  induction xs as [|k xs IH]; intros ys Hx Hy Heq.
  - destruct ys as [|l ys].
    + reflexivity.
    + exfalso.
      pose proof (sumF_cons_pos_valid l ys Hy) as Hpos.
      rewrite <- Heq in Hpos. simpl in Hpos. lia.
  - destruct ys as [|l ys].
    + exfalso.
      pose proof (sumF_cons_pos_valid k xs Hx) as Hpos.
      rewrite Heq in Hpos. simpl in Hpos. lia.
    + assert (Hk : k = l).
      {
        destruct (Nat.lt_ge_cases k l) as [Hkl|Hkge].
        - pose proof (sumF_lt_next_of_valid k xs Hx) as Hup.
          pose proof (sumF_ge_head l ys) as Hlow.
          rewrite Heq in Hup.
          assert (Hf : F (S k) <= F l).
          {
            apply F_succ_le_of_lt_ge2.
            - apply zeck_valid_head_ge_2 with (xs:=xs). exact Hx.
            - exact Hkl.
          }
          lia.
        - destruct (Nat.lt_ge_cases l k) as [Hlk|Hlge].
          + pose proof (sumF_lt_next_of_valid l ys Hy) as Hup.
            pose proof (sumF_ge_head k xs) as Hlow.
            rewrite <- Heq in Hup.
            assert (Hf : F (S l) <= F k).
            {
              apply F_succ_le_of_lt_ge2.
              - apply zeck_valid_head_ge_2 with (xs:=ys). exact Hy.
              - exact Hlk.
            }
            lia.
          + lia.
      }
      subst l.
      apply f_equal.
      apply IH.
      * apply zeck_valid_tail with (k:=k). exact Hx.
      * apply zeck_valid_tail with (k:=k). exact Hy.
      * simpl in Heq. lia.
Qed.

Theorem Z0_of_sumF :
  forall xs, zeck_valid xs -> Z0 (sumF xs) = xs.
Proof.
  intros xs Hvalid.
  apply Zeckendorf_unique_core.
  - apply Z0_valid.
  - exact Hvalid.
  - apply Z0_sound.
Qed.

Theorem Zeckendorf_unique :
  forall xs ys,
    zeck_valid xs ->
    zeck_valid ys ->
    sumF xs = sumF ys ->
    xs = ys.
Proof.
  intros xs ys Hx Hy Heq.
  rewrite <- (Z0_of_sumF xs Hx).
  rewrite <- (Z0_of_sumF ys Hy).
  f_equal.
  exact Heq.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Bridge to Carryless Pairing (P0)                                     *)
(*                                                                       *)
(*************************************************************************)

Lemma sumF_app : forall xs ys, sumF (xs ++ ys) = sumF xs + sumF ys.
Proof.
  induction xs as [|a xs IH]; intro ys; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Lemma all_ge_2_in :
  forall xs k, all_ge_2 xs -> In k xs -> 2 <= k.
Proof.
  induction xs as [|a xs IH]; intros k Hge Hin; simpl in *.
  - contradiction.
  - destruct Hge as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma all_le_in :
  forall m xs k, all_le m xs -> In k xs -> k <= m.
Proof.
  induction xs as [|a xs IH]; intros k Hle Hin; simpl in *.
  - contradiction.
  - destruct Hle as [Ha Hxs].
    destruct Hin as [<-|Hin].
    + exact Ha.
    + apply (IH k Hxs Hin).
Qed.

Lemma sumF_in_ge :
  forall xs k, In k xs -> F k <= sumF xs.
Proof.
  induction xs as [|a xs IH]; intros k Hin; simpl in *.
  - contradiction.
  - destruct Hin as [<-|Hin].
    + lia.
    + specialize (IH k Hin). lia.
Qed.

Lemma Z0_indices_below_r0 :
  forall x e,
    In e (Z0 x) ->
    e < r0 x.
Proof.
  intros x e Hin.
  unfold Z0 in Hin.
  destruct (zeck_greedy_down (r0 x) x false) as [xs rem'] eqn:Hgd.
  simpl in Hin.
  pose proof (zeck_greedy_down_correct (r0 x) x false xs rem' Hgd)
    as [Hsum [_ [Hall _]]].
  assert (Hele : e <= r0 x).
  { apply (all_le_in (r0 x) xs e Hall Hin). }
  destruct (Nat.eq_dec e (r0 x)) as [Heq|Hneq].
  - subst e.
    assert (Hf_le : F (r0 x) <= sumF xs).
    { apply sumF_in_ge. exact Hin. }
    assert (Hf_le_x : F (r0 x) <= x) by lia.
    pose proof (r0_upper x) as Hru.
    lia.
  - lia.
Qed.

Lemma two_S : forall n, two (S n) = S (S (two n)).
Proof.
  intro n.
  unfold two.
  simpl.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.

Lemma is_even_two : forall n, is_even (two n) = true.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite two_S. simpl. exact IH.
Qed.

Lemma is_even_S_two_false : forall n, is_even (S (two n)) = false.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite two_S. simpl. exact IH.
Qed.

Lemma two_j_minus1_formula :
  forall j, two_j_minus1 j = 2 * j - 1.
Proof.
  intro j.
  unfold two_j_minus1.
  rewrite <- Nat.sub_1_r.
  unfold two.
  lia.
Qed.

Lemma two_j_minus1_lt :
  forall a b, b < a -> two_j_minus1 b < two_j_minus1 a.
Proof.
  intros a b Hlt.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_gap2 :
  forall a b, a >= b + 2 -> two_j_minus1 a >= two_j_minus1 b + 2.
Proof.
  intros a b Hgap.
  repeat rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma two_j_minus1_ge_1 :
  forall j, 1 <= j -> 1 <= two_j_minus1 j.
Proof.
  intros j Hj.
  rewrite two_j_minus1_formula.
  lia.
Qed.

Lemma is_even_two_plus :
  forall a n, is_even (two a + n) = is_even n.
Proof.
  induction a as [|a IH]; intro n.
  - simpl. reflexivity.
  - rewrite two_S. simpl. apply IH.
Qed.

Lemma is_even_double_plus :
  forall a n, is_even (2 * a + n) = is_even n.
Proof.
  induction a as [|a IH]; intro n.
  - simpl. reflexivity.
  - replace (2 * S a + n) with (S (S (2 * a + n))) by lia.
    simpl.
    apply IH.
Qed.

Lemma is_even_two_j_minus1_false :
  forall j, 1 <= j -> is_even (two_j_minus1 j) = false.
Proof.
  intros j Hj.
  destruct j as [|j']; [lia|].
  unfold two_j_minus1.
  rewrite two_S.
  apply is_even_S_two_false.
Qed.

Lemma strictly_decreasing_map_two :
  forall xs, strictly_decreasing xs -> strictly_decreasing (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_two :
  forall xs, no_adjacent xs -> no_adjacent (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_two :
  forall xs, all_ge_2 xs -> all_ge_2 (map two xs).
Proof.
  induction xs as [|a xs IH]; intro Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - unfold two. lia.
  - apply IH. exact Htail.
Qed.

Lemma strictly_decreasing_map_odd :
  forall Bx xs,
    strictly_decreasing xs ->
    strictly_decreasing (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hdec.
  revert Bx Hdec.
  induction xs as [|a xs IH]; intros Bx Hdec; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hdec as [Hab Htail].
  split.
  - apply Nat.add_lt_mono_l. apply two_j_minus1_lt. exact Hab.
  - apply IH. exact Htail.
Qed.

Lemma no_adjacent_map_odd :
  forall Bx xs,
    no_adjacent xs ->
    no_adjacent (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hadj.
  revert Bx Hadj.
  induction xs as [|a xs IH]; intros Bx Hadj; simpl; auto.
  destruct xs as [|b xs']; simpl in *; auto.
  destruct Hadj as [Hab Htail].
  split.
  - assert (Hgap : two_j_minus1 a >= two_j_minus1 b + 2).
    { apply two_j_minus1_gap2. exact Hab. }
    lia.
  - apply IH. exact Htail.
Qed.

Lemma all_ge_2_map_odd :
  forall Bx xs,
    all_ge_2 xs ->
    all_ge_2 (map (fun j => Bx + two_j_minus1 j) xs).
Proof.
  intros Bx xs Hge.
  revert Bx Hge.
  induction xs as [|a xs IH]; intros Bx Hge; simpl; auto.
  destruct Hge as [Ha Htail].
  split.
  - rewrite two_j_minus1_formula.
    lia.
  - apply IH. exact Htail.
Qed.

Lemma even_band_valid :
  forall x, zeck_valid (even_band P0 x).
Proof.
  intro x.
  unfold even_band, P0.
  pose proof (Z0_valid x) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_two. exact Hdec.
  - split.
    + apply no_adjacent_map_two. exact Hadj.
    + apply all_ge_2_map_two. exact Hge.
Qed.

Lemma odd_band_valid :
  forall x y, zeck_valid (odd_band P0 x y).
Proof.
  intros x y.
  unfold odd_band, P0.
  pose proof (Z0_valid y) as [Hdec [Hadj Hge]].
  split.
  - apply strictly_decreasing_map_odd. exact Hdec.
  - split.
    + apply no_adjacent_map_odd. exact Hadj.
    + apply all_ge_2_map_odd. exact Hge.
Qed.

Lemma even_band_lt_B :
  forall x e, In e (even_band P0 x) -> e < B P0 x.
Proof.
  intros x e Hin.
  unfold even_band, P0 in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [He Hj]].
  subst e.
  assert (Hjlt : j < r0 x).
  { apply Z0_indices_below_r0. exact Hj. }
  unfold P0.
  unfold B.
  unfold two.
  simpl.
  replace (2 * r0 x) with (r0 x + r0 x) by lia.
  lia.
Qed.

Lemma odd_band_ge_B1 :
  forall x y o, In o (odd_band P0 x y) -> S (B P0 x) <= o.
Proof.
  intros x y o Hin.
  unfold odd_band, P0 in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Ho Hj]].
  subst o.
  assert (Hj2 : 2 <= j).
  { apply all_ge_2_in with (xs:=Z0 y); [|exact Hj]. 
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge. }
  assert (Hj1 : 1 <= j) by lia.
  assert (Hodd1 : 1 <= two_j_minus1 j) by (apply two_j_minus1_ge_1; exact Hj1).
  unfold B.
  unfold P0.
  simpl.
  lia.
Qed.

Lemma odd_band_gt_even_band :
  forall x y o e,
    In o (odd_band P0 x y) ->
    In e (even_band P0 x) ->
    o > e.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma odd_band_gap_even_band :
  forall x y o e,
    In o (odd_band P0 x y) ->
    In e (even_band P0 x) ->
    o >= e + 2.
Proof.
  intros x y o e Ho He.
  pose proof (odd_band_ge_B1 x y o Ho) as Hob.
  pose proof (even_band_lt_B x e He) as Heb.
  lia.
Qed.

Lemma all_ge_2_app :
  forall xs ys, all_ge_2 xs -> all_ge_2 ys -> all_ge_2 (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy; simpl.
  - exact Hy.
  - destruct Hx as [Ha Hxs]. split; [exact Ha|]. apply IH; assumption.
Qed.

Lemma strictly_decreasing_app :
  forall xs ys,
    strictly_decreasing xs ->
    strictly_decreasing ys ->
    (forall x y, In x xs -> In y ys -> x > y) ->
    strictly_decreasing (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

Lemma no_adjacent_app :
  forall xs ys,
    no_adjacent xs ->
    no_adjacent ys ->
    (forall x y, In x xs -> In y ys -> x >= y + 2) ->
    no_adjacent (xs ++ ys).
Proof.
  induction xs as [|a xs IH]; intros ys Hx Hy Hcross; simpl.
  - exact Hy.
  - destruct xs as [|b xs'].
    + simpl.
      destruct ys as [|y ys'].
      * simpl. exact I.
      * simpl. split.
        -- apply Hcross; simpl; auto.
        -- exact Hy.
    + simpl in Hx.
      destruct Hx as [Hab Htail].
      simpl.
      split; [exact Hab|].
      apply IH; try assumption.
      intros x y Hinx Hiny.
      apply Hcross; simpl; auto.
Qed.

Lemma odd_even_concat_valid :
  forall x y,
    zeck_valid (odd_band P0 x y ++ even_band P0 x).
Proof.
  intros x y.
  pose proof (odd_band_valid x y) as [Hdec_o [Hadj_o Hge_o]].
  pose proof (even_band_valid x) as [Hdec_e [Hadj_e Hge_e]].
  split.
  - eapply strictly_decreasing_app; eauto.
    intros o e Ho He.
    apply odd_band_gt_even_band with (x:=x) (y:=y); assumption.
  - split.
    + eapply no_adjacent_app; eauto.
      intros o e Ho He.
      apply odd_band_gap_even_band with (x:=x) (y:=y); assumption.
    + apply all_ge_2_app; assumption.
Qed.

Lemma pair_P0_as_odd_even_sum :
  forall x y,
    pair P0 x y = sumF (odd_band P0 x y ++ even_band P0 x).
Proof.
  intros x y.
  unfold pair.
  rewrite !sumF_app.
  lia.
Qed.

Theorem Z0_pair_is_concat :
  forall x y,
    Z0 (pair P0 x y) = odd_band P0 x y ++ even_band P0 x.
Proof.
  intros x y.
  rewrite pair_P0_as_odd_even_sum.
  apply Z0_of_sumF.
  apply odd_even_concat_valid.
Qed.

Lemma even_band_even :
  forall x k,
    In k (even_band P0 x) ->
    is_even k = true.
Proof.
  intros x k Hin.
  unfold even_band, P0 in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e [He _]].
  subst k.
  apply is_even_two.
Qed.

Lemma odd_band_even_false :
  forall x y k,
    In k (odd_band P0 x y) ->
    is_even k = false.
Proof.
  intros x y k Hin.
  unfold odd_band, P0 in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Hk Hj]].
  subst k.
  assert (Hj2 : 2 <= j).
  { apply all_ge_2_in with (xs:=Z0 y); [|exact Hj].
    destruct (Z0_valid y) as [_ [_ Hge]]; exact Hge. }
  assert (Hj1 : 1 <= j) by lia.
  unfold B.
  rewrite is_even_double_plus.
  apply is_even_two_j_minus1_false.
  exact Hj1.
Qed.

Lemma odd_band_odd_ge_B1_true :
  forall x y k,
    In k (odd_band P0 x y) ->
    odd_ge_B1 (B P0 x) k = true.
Proof.
  intros x y k Hin.
  unfold odd_ge_B1.
  unfold is_odd.
  rewrite (odd_band_even_false x y k Hin).
  apply Nat.leb_le.
  apply (odd_band_ge_B1 x y k).
  exact Hin.
Qed.

Lemma even_band_odd_ge_B1_false :
  forall x k,
    In k (even_band P0 x) ->
    odd_ge_B1 (B P0 x) k = false.
Proof.
  intros x k Hin.
  unfold odd_ge_B1.
  unfold is_odd.
  rewrite (even_band_even x k Hin).
  reflexivity.
Qed.

Lemma filter_false_nil :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = false) ->
    filter p xs = [].
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = false) by (apply Hp; simpl; auto).
    rewrite Ha.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

Lemma filter_true_id :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (forall a, In a xs -> p a = true) ->
    filter p xs = xs.
Proof.
  intros A p xs Hp.
  induction xs as [|a xs IH]; simpl.
  - reflexivity.
  - assert (Ha : p a = true) by (apply Hp; simpl; auto).
    rewrite Ha.
    simpl.
    f_equal.
    apply IH.
    intros b Hb.
    apply Hp.
    simpl; auto.
Qed.

Corollary Z0_even_split :
  forall x y,
    filter is_even (Z0 (pair P0 x y)) = even_band P0 x.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_nil : filter is_even (odd_band P0 x y) = []).
  { apply filter_false_nil. intros a Ha. apply (odd_band_even_false x y a); exact Ha. }
  assert (Heven_id : filter is_even (even_band P0 x) = even_band P0 x).
  { apply filter_true_id. intros a Ha. apply (even_band_even x a); exact Ha. }
  rewrite Hodd_nil, Heven_id. reflexivity.
Qed.

Corollary Z0_odd_split :
  forall x y,
    filter (odd_ge_B1 (B P0 x)) (Z0 (pair P0 x y)) = odd_band P0 x y.
Proof.
  intros x y.
  rewrite Z0_pair_is_concat.
  rewrite filter_app.
  assert (Hodd_id :
    filter (odd_ge_B1 (B P0 x)) (odd_band P0 x y) = odd_band P0 x y).
  { apply filter_true_id. intros a Ha. apply (odd_band_odd_ge_B1_true x y a); exact Ha. }
  assert (Heven_nil :
    filter (odd_ge_B1 (B P0 x)) (even_band P0 x) = []).
  { apply filter_false_nil. intros a Ha. apply (even_band_odd_ge_B1_false x a); exact Ha. }
  rewrite Hodd_id, Heven_nil.
  rewrite app_nil_r.
  reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Fibonacci-Banded Support Window (R12 helper)                         *)
(*                                                                       *)
(*************************************************************************)

Definition fib_band (b x : nat) : list nat :=
  map (fun j => b + j) (Z0 x).

Lemma r0_le_of_lt_F :
  forall x K,
    x < F K ->
    r0 x <= K.
Proof.
  intros x K Hx.
  destruct (le_gt_dec (r0 x) K) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    assert (HK : K < r0 x) by lia.
    pose proof (r0_minimal x K HK) as HKmin.
    lia.
Qed.

Lemma Z0_index_lt_of_lt_F :
  forall x K i,
    x < F K ->
    In i (Z0 x) ->
    i < K.
Proof.
  intros x K i Hx Hin.
  pose proof (Z0_indices_below_r0 x i Hin) as Hir0.
  pose proof (r0_le_of_lt_F x K Hx) as Hr0.
  lia.
Qed.

Lemma Z0_index_ge_2 :
  forall x i,
    In i (Z0 x) ->
    2 <= i.
Proof.
  intros x i Hin.
  apply all_ge_2_in with (xs := Z0 x).
  - destruct (Z0_valid x) as [_ [_ Hge]].
    exact Hge.
  - exact Hin.
Qed.

Lemma fib_band_support_window :
  forall b K x i,
    x < F K ->
    In i (fib_band b x) ->
    b + 2 <= i /\ i < b + K.
Proof.
  intros b K x i Hx Hin.
  unfold fib_band in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [j [Hij Hj]].
  subst i.
  split.
  - pose proof (Z0_index_ge_2 x j Hj) as Hj2.
    lia.
  - pose proof (Z0_index_lt_of_lt_F x K j Hx Hj) as HjK.
    lia.
Qed.

Lemma fib_band_no_overlap :
  forall b1 b2 K x y i1 i2,
    x < F K ->
    y < F K ->
    b1 + K <= b2 ->
    In i1 (fib_band b1 x) ->
    In i2 (fib_band b2 y) ->
    i1 + 1 < i2.
Proof.
  intros b1 b2 K x y i1 i2 Hx Hy Hsep Hin1 Hin2.
  pose proof (fib_band_support_window b1 K x i1 Hx Hin1) as [_ Hi1].
  pose proof (fib_band_support_window b2 K y i2 Hy Hin2) as [Hi2 _].
  lia.
Qed.