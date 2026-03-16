(* R06__Mixed_Periodicity.v *)

From Coq Require Import Arith Bool Classical_Prop Lia List ZArith.
Import ListNotations.

From T004 Require Import
  R00__Base
  R01__Seed
  R02__Local_Lemmas.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 3 — Mixed Periodicity                      *)
(*                                                                       *)
(*  Phase 3 starts from eventual repetition after a finite cutoff.       *)
(*  The first bridge is finite and local: an eventual-periodicity        *)
(*  witness yields an infinite family of repeated local predecessor      *)
(*  problems at one fixed cutoff phase.                                  *)
(*                                                                       *)
(*************************************************************************)

Section Mixed_Periodicity.

Definition row_window (r : row) (radius : nat) : list bit :=
  map r (centered_coords radius).

Definition eventually_periodic_center_window (n : nat) : Prop :=
  exists T P,
    (0 < P)%nat /\
    forall t,
      center_window n (T + t + P)%nat = center_window n (T + t)%nat.

Definition observational_periodic_tail_from (R T P : nat) : Prop :=
  (0 < P)%nat /\
  forall t,
    center_window R (T + t + P)%nat = center_window R (T + t)%nat.

Definition uniformly_eventually_periodic_from (R T P : nat) : Prop :=
  (0 < P)%nat /\
  forall extra t,
    center_window (R + extra) (T + t + P)%nat =
    center_window (R + extra) (T + t)%nat.

Definition realizable_uniform_periodic_tail_from (R : nat) : Prop :=
  exists T P, uniformly_eventually_periodic_from R T P.

Definition bhk_window_upgrade_principle : Prop :=
  forall R T P,
    observational_periodic_tail_from R T P ->
    uniformly_eventually_periodic_from R T P.

Definition faithful_window_growth_principle : Prop :=
  forall R T P,
    observational_periodic_tail_from R T P ->
    observational_periodic_tail_from (S R) T P.

Record faithful_observational_periodic_tail_realizer (R : nat) : Type := {
  foptr_start : nat;
  foptr_period : nat;
  foptr_observational :
    observational_periodic_tail_from R foptr_start foptr_period;
  foptr_uniform :
    uniformly_eventually_periodic_from R foptr_start foptr_period
}.

Definition realizable_observational_periodic_tail_from (R : nat) : Prop :=
  inhabited (faithful_observational_periodic_tail_realizer R).

Definition eventually_periodic_full_rows_from (T P : nat) : Prop :=
  (0 < P)%nat /\
  forall t x,
    canonical_row (T + t + P)%nat x = canonical_row (T + t)%nat x.

Definition finite_periodic_orbit (n T P K : nat) : Prop :=
  (0 < P)%nat /\
  forall m,
    (m <= K)%nat ->
    center_window n (T + m * P)%nat = center_window n T.

Definition finite_repeat_block (n T P K : nat) : Prop :=
  (0 < P)%nat /\
  forall s,
    (s <= K)%nat ->
    center_window n (T + P + s)%nat = center_window n (T + s)%nat.

Definition small_backward_pair_block
    (R T P extra : nat) (ij : nat * nat) : Prop :=
  let (i, j) := ij in
  (i < j)%nat /\
  (j <= 4)%nat /\
  forall s,
    (s <= extra)%nat ->
    center_window (S R) (T + (S i) * P + s)%nat =
    center_window (S R) (T + (S j) * P + s)%nat.

Definition local_target_window_realization
    (R : nat) (v u : row) : Prop :=
  row_window (step u) R = row_window v R.

Definition predecessor_carrier_window (R : nat) (u : row) : list bit :=
  row_window u (S R).

Definition predecessor_carrier_length (R : nat) : nat :=
  S (2 * S R).

Fixpoint rule30_window_from (a b : bit) (xs : list bit) : list bit :=
  match xs with
  | c :: rest =>
      rule30 a b c :: rule30_window_from b c rest
  | [] => []
  end.

Definition rule30_window (xs : list bit) : list bit :=
  match xs with
  | a :: b :: rest => rule30_window_from a b rest
  | _ => []
  end.

Definition recover_left_bit (o b c : bit) : bit :=
  xorb o (orb b c).

Definition cutoff_predecessor (T P m : nat) : row :=
  canonical_row (T + m * P + (P - 1))%nat.

Definition cutoff_predecessor_carrier (R T P m : nat) : list bit :=
  predecessor_carrier_window R (cutoff_predecessor T P m).

Definition carrier_realizes_window
    (R : nat) (target_window carrier : list bit) : Prop :=
  length carrier = predecessor_carrier_length R /\
  rule30_window carrier = target_window.

Definition canonical_cutoff_window (R T : nat) : list bit :=
  center_window R T.

Definition finite_carrier_memory_orbit (R T P K : nat) : Prop :=
  forall m,
    (m <= K)%nat ->
    carrier_realizes_window R (canonical_cutoff_window R T)
      (cutoff_predecessor_carrier R T P m).

Definition backward_transport_carrier_orbit (R T P K : nat) : Prop :=
  forall m,
    (m <= K)%nat ->
    carrier_realizes_window R (canonical_cutoff_window R (S T))
      (predecessor_carrier_window R (canonical_row (T + (S m) * P)%nat)).

Definition repeated_cutoff_predecessor_carrier (R T P K : nat) : Prop :=
  exists i j,
    (i < j)%nat /\
    (j <= K)%nat /\
    cutoff_predecessor_carrier R T P i =
    cutoff_predecessor_carrier R T P j.

Fixpoint all_bit_lists (len : nat) : list (list bit) :=
  match len with
  | O => [[]]
  | S len' =>
      map (cons false) (all_bit_lists len') ++
      map (cons true) (all_bit_lists len')
  end.

Definition carrier_pool (R : nat) : list (list bit) :=
  all_bit_lists (predecessor_carrier_length R).

Definition carrier_right_boundary_signature (carrier : list bit) : bit * bit :=
  match rev carrier with
  | c :: b :: _ => (b, c)
  | _ => (false, false)
  end.

Definition boundary_signature_pool : list (bit * bit) :=
  [(false, false); (false, true); (true, false); (true, true)].

Fixpoint reconstruct_carrier_from_rev
    (outs_rev : list bit) (b c : bit) : list bit :=
  match outs_rev with
  | [] => [b; c]
  | o :: rest =>
      let a := recover_left_bit o b c in
      reconstruct_carrier_from_rev rest a b ++ [c]
  end.

Definition reconstruct_carrier_from_right
    (target : list bit) (b c : bit) : list bit :=
  reconstruct_carrier_from_rev (rev target) b c.

Fixpoint rule30_window_rev_from
    (b c : bit) (left_rev : list bit) : list bit :=
  match left_rev with
  | [] => []
  | a :: rest =>
      rule30 a b c :: rule30_window_rev_from a b rest
  end.

Definition rule30_window_rev (xs_rev : list bit) : list bit :=
  match xs_rev with
  | c :: b :: rest => rule30_window_rev_from b c rest
  | _ => []
  end.

Fixpoint reconstruct_carrier_rev_from
    (outs_rev : list bit) (b c : bit) : list bit :=
  match outs_rev with
  | [] => [c; b]
  | o :: rest =>
      let a := recover_left_bit o b c in
      c :: reconstruct_carrier_rev_from rest a b
  end.

Definition reconstruct_carrier_rev
    (target : list bit) (b c : bit) : list bit :=
  reconstruct_carrier_rev_from (rev target) b c.

Lemma NoDup_map_injective :
  forall (A B : Type) (f : A -> B) xs,
    NoDup xs ->
    (forall x y, f x = f y -> x = y) ->
    NoDup (map f xs).
Proof.
  intros A B f xs Hnodup Hinj.
  induction Hnodup as [|x xs Hnotin Hnodup IH].
  - simpl.
    constructor.
  - simpl.
    constructor.
    + intro Hin.
      apply in_map_iff in Hin.
      destruct Hin as [y [Hfy Hy]].
      apply Hnotin.
      apply Hinj in Hfy.
      subst y.
      exact Hy.
    + exact IH.
Qed.

Theorem pigeonhole_typed :
  forall (A B : Type) (eq_dec : forall x y : B, {x = y} + {x <> y})
         (f : A -> B) (xs : list A) (cats : list B),
    NoDup xs ->
    (forall x, In x xs -> In (f x) cats) ->
    (length cats < length xs)%nat ->
    exists a b,
      In a xs /\
      In b xs /\
      a <> b /\
      f a = f b.
Proof.
  intros A B eq_dec f xs.
  induction xs as [|x xs IH]; intros cats Hnodup Hcat Hlen.
  - simpl in Hlen.
    lia.
  - apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hnotin_x Hnodup_xs].
    destruct (in_dec eq_dec (f x) (map f xs)) as [Hin | Hnotin].
    + apply in_map_iff in Hin.
      destruct Hin as [y [Hy_eq Hy_in]].
      exists x, y.
      repeat split.
      * simpl.
        left.
        reflexivity.
      * simpl.
        right.
        exact Hy_in.
      * intro Hxy.
        subst y.
        contradiction.
      * symmetry.
        exact Hy_eq.
    + assert (Hcat_xs :
          forall y, In y xs -> In (f y) (remove eq_dec (f x) cats)).
      { intros y Hy.
        specialize (Hcat y (or_intror Hy)) as Hy_cat.
        assert (Hy_map : In (f y) (map f xs)).
        { apply in_map.
          exact Hy. }
        assert (Hneq_fx : f y <> f x).
        { intro Heq.
          rewrite Heq in Hy_map.
          contradiction. }
        eapply in_in_remove.
        - exact Hneq_fx.
        - exact Hy_cat. }
      assert (Hlen_xs : (length (remove eq_dec (f x) cats) < length xs)%nat).
      { specialize (Hcat x (or_introl eq_refl)) as Hfx_cat.
        pose proof (remove_length_lt eq_dec cats (f x) Hfx_cat) as Hrm.
        simpl in Hlen.
        lia. }
      specialize (IH (remove eq_dec (f x) cats) Hnodup_xs Hcat_xs Hlen_xs).
      destruct IH as [a [b [Ha [Hb [Hab Hf]]]]].
      exists a, b.
      repeat split.
      * simpl.
        right.
        exact Ha.
      * simpl.
        right.
        exact Hb.
      * exact Hab.
      * exact Hf.
Qed.

Theorem finite_list_has_arbitrarily_often_member :
  forall (A : Type) (xs : list A) (Q : A -> nat -> Prop),
    (forall N, exists x, In x xs /\ exists n, (N <= n)%nat /\ Q x n) ->
    exists x, In x xs /\ forall N, exists n, (N <= n)%nat /\ Q x n.
Proof.
  intros A xs.
  induction xs as [|x xs IH]; intros Q Hall.
  - specialize (Hall 0%nat).
    destruct Hall as [y [Hin _]].
    inversion Hin.
  - destruct (classic (forall N, exists n, (N <= n)%nat /\ Q x n))
      as [Hx_far | Hx_not_far].
    + exists x.
      split.
      * left.
        reflexivity.
      * exact Hx_far.
    + assert (Hbound : exists N0, forall n, (N0 <= n)%nat -> ~ Q x n).
      { apply NNPP.
        intro Hno_bound.
        apply Hx_not_far.
        intro N.
        apply NNPP.
        intro HN.
        apply Hno_bound.
        exists N.
        intros n HNn HQ.
        apply HN.
        exists n.
        split; assumption. }
      destruct Hbound as [N0 Hbound].
      assert (Hall_tail :
          forall N, exists y, In y xs /\ exists n, (N <= n)%nat /\ Q y n).
      { intro N.
        specialize (Hall (Nat.max N N0)).
        destruct Hall as [y [Hy [n [Hmax HQ]]]].
        destruct Hy as [Hy | Hy].
        - subst y.
          exfalso.
          apply (Hbound n).
          + eapply Nat.le_trans.
            * apply Nat.le_max_r.
            * exact Hmax.
          + exact HQ.
        - exists y.
          split.
          + exact Hy.
          + exists n.
            split.
            * eapply Nat.le_trans.
              -- apply Nat.le_max_l.
              -- exact Hmax.
            * exact HQ.
      }
      destruct (IH Q Hall_tail) as [y [Hy Hfar]].
      exists y.
      split.
      * right.
        exact Hy.
      * exact Hfar.
Qed.

Definition bounded_transport_pair_pool (T P : nat) : list (nat * nat) :=
  flat_map
    (fun dt =>
       map (fun P' => ((T + P + dt)%nat, P')) (seq 1 (4 * P)%nat))
    (seq 0 (S (3 * P))%nat).

Lemma bounded_transport_pair_pool_complete :
  forall T P T' P',
    (T + P <= T')%nat ->
    (T' <= T + 4 * P)%nat ->
    (0 < P' <= 4 * P)%nat ->
    In (T', P') (bounded_transport_pair_pool T P).
Proof.
  intros T P T' P' Hlow Hhigh [HP' Hbound].
  unfold bounded_transport_pair_pool.
  apply in_flat_map.
  exists (T' - (T + P))%nat.
  split.
  - apply in_seq.
    lia.
  - apply in_map_iff.
    exists P'.
    split.
    + f_equal.
      lia.
    + apply in_seq.
      lia.
Qed.

Lemma bounded_transport_pair_pool_sound :
  forall T P T' P',
    In (T', P') (bounded_transport_pair_pool T P) ->
    (T + P <= T')%nat /\
    (T' <= T + 4 * P)%nat /\
    (0 < P' <= 4 * P)%nat.
Proof.
  intros T P T' P' Hin.
  unfold bounded_transport_pair_pool in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [dt [Hdt Hpair]].
  apply in_seq in Hdt.
  destruct Hdt as [Hdt_lo Hdt_hi].
  apply in_map_iff in Hpair.
  destruct Hpair as [p [Hp_eq Hp_in]].
  inversion Hp_eq; subst p.
  apply in_seq in Hp_in.
  destruct Hp_in as [Hp_lo Hp_hi].
  repeat split; lia.
Qed.

Lemma uniformly_eventually_periodic_from_shift_radius :
  forall R T P base_extra,
    uniformly_eventually_periodic_from R T P ->
    uniformly_eventually_periodic_from (R + base_extra) T P.
Proof.
  intros R T P base_extra [HP Hperiod].
  split.
  - exact HP.
  - intros extra t.
    replace (R + base_extra + extra)%nat with (R + (base_extra + extra))%nat
      by lia.
    exact (Hperiod (base_extra + extra)%nat t).
Qed.

Definition bit_pair_eq_dec :
  forall x y : bit * bit, {x = y} + {x <> y}.
Proof.
  decide equality; apply Bool.bool_dec.
Defined.

Definition nat_pair_eq_dec :
  forall x y : nat * nat, {x = y} + {x <> y}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Lemma rule30_recovers_left_bit :
  forall o b c,
    rule30 (recover_left_bit o b c) b c = o.
Proof.
  intros o b c.
  unfold recover_left_bit, rule30.
  destruct o, b, c; reflexivity.
Qed.

Lemma recover_left_bit_unique :
  forall a o b c,
    rule30 a b c = o ->
    a = recover_left_bit o b c.
Proof.
  intros a o b c H.
  unfold recover_left_bit, rule30 in *.
  destruct a, o, b, c; inversion H; reflexivity.
Qed.

Lemma reconstruct_carrier_rev_from_length :
  forall outs_rev b c,
    length (reconstruct_carrier_rev_from outs_rev b c) =
    S (S (length outs_rev)).
Proof.
  induction outs_rev as [|o outs_rev IH]; intros b c.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma reconstruct_carrier_rev_from_starts_with_boundary :
  forall outs_rev b c,
    exists rest,
      reconstruct_carrier_rev_from outs_rev b c = c :: b :: rest.
Proof.
  induction outs_rev as [|o outs_rev IH]; intros b c.
  - exists [].
    reflexivity.
  - simpl.
    destruct (IH (recover_left_bit o b c) b) as [rest Hrest].
    rewrite Hrest.
    exists ((recover_left_bit o b c) :: rest).
    reflexivity.
Qed.

Theorem rule30_window_rev_reconstructs_outputs :
  forall outs_rev b c,
    rule30_window_rev (reconstruct_carrier_rev_from outs_rev b c) = outs_rev.
Proof.
  induction outs_rev as [|o outs_rev IH]; intros b c.
  - reflexivity.
  - simpl.
    destruct
      (reconstruct_carrier_rev_from_starts_with_boundary
        outs_rev (recover_left_bit o b c) b)
      as [rest Hrest].
    rewrite Hrest.
    simpl.
    rewrite rule30_recovers_left_bit.
    f_equal.
    change
      (rule30_window_rev
         (b :: recover_left_bit o b c :: rest) = outs_rev).
    rewrite <- Hrest.
    exact (IH (recover_left_bit o b c) b).
Qed.

Theorem rule30_window_rev_determined_by_boundary :
  forall outs_rev b c rest,
    rule30_window_rev (c :: b :: rest) = outs_rev ->
    c :: b :: rest = reconstruct_carrier_rev_from outs_rev b c.
Proof.
  induction outs_rev as [|o outs_rev IH]; intros b c rest Hout.
  - destruct rest as [|a rest].
    + reflexivity.
    + simpl in Hout.
      discriminate Hout.
  - destruct rest as [|a rest].
    + simpl in Hout.
      discriminate Hout.
    + simpl in Hout.
      injection Hout as Hhead Htail.
      pose proof (recover_left_bit_unique a o b c Hhead) as Ha.
      subst a.
      simpl.
      f_equal.
      exact (IH (recover_left_bit o b c) b rest Htail).
Qed.

Lemma nth_error_map_some :
  forall (A B : Type) (f : A -> B) xs i x,
    nth_error xs i = Some x ->
    nth_error (map f xs) i = Some (f x).
Proof.
  intros A B f xs.
  induction xs as [|a xs IH]; intros i x Hnth.
  - destruct i; inversion Hnth.
  - destruct i as [|i].
    + simpl in Hnth.
      inversion Hnth; subst.
      reflexivity.
    + simpl in Hnth.
      simpl.
      exact (IH i x Hnth).
Qed.

Lemma z_segment_length :
  forall start len,
    length (z_segment start len) = len.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intro start.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Fixpoint z_segment_desc (start : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => []
  | S len' => start :: z_segment_desc (start - 1) len'
  end.

Lemma z_segment_desc_last :
  forall len stop,
    z_segment_desc stop (S len) =
    z_segment_desc stop len ++ [stop - Z.of_nat len].
Proof.
  induction len as [|len IH]; intro stop.
  - simpl.
    replace (stop - 0)%Z with stop by lia.
    reflexivity.
  - simpl.
    f_equal.
    change ((stop - 1) :: z_segment_desc (stop - 1 - 1) len)
      with (z_segment_desc (stop - 1) (S len)).
    rewrite (IH (stop - 1)).
    assert (Hlast : (stop - 1 - Z.of_nat len = stop - Z.of_nat (S len))%Z)
      by lia.
    rewrite Hlast.
    reflexivity.
Qed.

Lemma z_segment_desc_snoc :
  forall start len,
    z_segment_desc (start + Z.of_nat len) (S len) =
    z_segment_desc (start + Z.of_nat len) len ++ [start].
Proof.
  intros start len.
  rewrite z_segment_desc_last.
  assert (Hlast : (start + Z.of_nat len - Z.of_nat len = start)%Z) by lia.
  rewrite Hlast.
  reflexivity.
Qed.

Lemma rev_z_segment :
  forall start len,
    rev (z_segment start len) =
    z_segment_desc (start + Z.of_nat len - 1) len.
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intro start.
  - reflexivity.
  - simpl.
    rewrite (IH (start + 1)).
    replace (start + 1 + Z.of_nat len - 1)%Z with (start + Z.of_nat len)%Z
      by lia.
    replace (start + Z.pos (Pos.of_succ_nat len) - 1)%Z
      with (start + Z.of_nat len)%Z by lia.
    replace (start + Z.pos (Pos.of_succ_nat len) - 1 - 1)%Z
      with (start + Z.of_nat len - 1)%Z by lia.
    change
      ((start + Z.of_nat len)
        :: z_segment_desc (start + Z.of_nat len - 1) len)
      with (z_segment_desc (start + Z.of_nat len) (S len)).
    symmetry.
    apply z_segment_desc_snoc.
Qed.

Lemma z_segment_in_bounds :
  forall start len x,
    In x (z_segment start len) ->
    (start <= x < start + Z.of_nat len)%Z.
Proof.
  intros start len x Hin.
  revert start x Hin.
  induction len as [|len IH]; intros start x Hin.
  - inversion Hin.
  - simpl in Hin.
    destruct Hin as [Hx | Hin].
    + subst x.
      split; lia.
    + specialize (IH (start + 1)%Z x Hin).
      lia.
Qed.

Lemma centered_coords_length :
  forall R,
    length (centered_coords (S R)) = predecessor_carrier_length R.
Proof.
  intro R.
  unfold centered_coords, predecessor_carrier_length.
  rewrite z_segment_length.
  reflexivity.
Qed.

Lemma rev_centered_coords :
  forall R,
    rev (centered_coords R) =
    z_segment_desc (Z.of_nat R) (S (2 * R)).
Proof.
  intro R.
  unfold centered_coords.
  rewrite rev_z_segment.
  f_equal.
  lia.
Qed.

Lemma all_bit_lists_length :
  forall len,
    length (all_bit_lists len) = Nat.pow 2 len.
Proof.
  induction len as [|len IH].
  - reflexivity.
  - simpl.
    rewrite length_app.
    repeat rewrite length_map.
    setoid_rewrite IH.
    simpl Nat.pow.
    lia.
Qed.

Lemma all_bit_lists_complete :
  forall len xs,
    length xs = len ->
    In xs (all_bit_lists len).
Proof.
  induction len as [|len IH]; intros xs Hlen.
  - destruct xs as [|x xs].
    + simpl.
      left.
      reflexivity.
    + discriminate Hlen.
  - destruct xs as [|x xs].
    + discriminate Hlen.
    + simpl in Hlen.
      simpl.
      destruct x.
      * apply in_app_iff.
        right.
        apply in_map.
        apply IH.
        lia.
      * apply in_app_iff.
        left.
        apply in_map.
        apply IH.
        lia.
Qed.

Lemma all_bit_lists_NoDup :
  forall len,
    NoDup (all_bit_lists len).
Proof.
  induction len as [|len IH].
  - simpl.
    constructor.
    + intro Hin.
      inversion Hin.
    + constructor.
  - simpl.
    apply NoDup_app.
    + apply NoDup_map_injective with (f := cons false).
      * exact IH.
      * intros x y Hxy.
        inversion Hxy.
        reflexivity.
    + apply NoDup_map_injective with (f := cons true).
      * exact IH.
      * intros x y Hxy.
        inversion Hxy.
        reflexivity.
    + intros x Hfalse Htrue.
      apply in_map_iff in Hfalse.
      apply in_map_iff in Htrue.
      destruct Hfalse as [xs [Hxs _]].
      destruct Htrue as [ys [Hys _]].
      rewrite <- Hxs in Hys.
      discriminate Hys.
Qed.

Lemma carrier_pool_complete :
  forall R xs,
    length xs = predecessor_carrier_length R ->
    In xs (carrier_pool R).
Proof.
  intros R xs Hlen.
  unfold carrier_pool.
  apply all_bit_lists_complete.
  exact Hlen.
Qed.

Lemma carrier_pool_length :
  forall R,
    length (carrier_pool R) = Nat.pow 2 (predecessor_carrier_length R).
Proof.
  intro R.
  unfold carrier_pool.
  apply all_bit_lists_length.
Qed.

Lemma predecessor_carrier_window_length :
  forall R u,
    length (predecessor_carrier_window R u) = predecessor_carrier_length R.
Proof.
  intros R u.
  unfold predecessor_carrier_window, row_window.
  rewrite length_map.
  apply centered_coords_length.
Qed.

Lemma rule30_window_rev_from_on_desc_segment :
  forall r start len,
    rule30_window_rev_from (r (start - 1)) (r start)
      (map r (z_segment_desc (start - 2) len)) =
    map (step r) (z_segment_desc (start - 1) len).
Proof.
  intros r start len.
  revert start.
  induction len as [|len IH]; intro start.
  - reflexivity.
  - simpl.
    unfold step, step_row.
    replace (start - 1 - 1)%Z with (start - 2)%Z by lia.
    replace (start - 1 + 1)%Z with start by lia.
    f_equal.
    replace (start - 2 - 1)%Z with (start - 3)%Z by lia.
    replace (start - 2)%Z with ((start - 1) - 1)%Z by lia.
    pose proof (IH (start - 1)) as IH'.
    replace (start - 1 - 2)%Z with (start - 3)%Z in IH' by lia.
    exact IH'.
Qed.

Lemma rule30_window_rev_on_desc_segment :
  forall r start len,
    rule30_window_rev (map r (z_segment_desc start (S (S len)))) =
    map (step r) (z_segment_desc (start - 1) len).
Proof.
  intros r start len.
  simpl.
  replace (start - 1 - 1)%Z with (start - 2)%Z by lia.
  exact (rule30_window_rev_from_on_desc_segment r start len).
Qed.

Lemma rule30_window_rev_on_centered_carrier :
  forall R u,
    rule30_window_rev (rev (predecessor_carrier_window R u)) =
    rev (row_window (step u) R).
Proof.
  intros R u.
  unfold predecessor_carrier_window, row_window.
  rewrite <- map_rev.
  rewrite rev_centered_coords.
  replace (S (2 * S R)) with (S (S (S (2 * R)))) by lia.
  rewrite rule30_window_rev_on_desc_segment.
  replace (Z.of_nat (S R) - 1)%Z with (Z.of_nat R)%Z by lia.
  rewrite <- map_rev.
  rewrite rev_centered_coords.
  reflexivity.
Qed.

Lemma rule30_window_from_on_segment :
  forall r start len,
    rule30_window_from (r start) (r (start + 1))
      (map r (z_segment (start + 2) len)) =
    map (step r) (z_segment (start + 1) len).
Proof.
  intros r start len.
  revert start.
  induction len as [|len IH]; intro start.
  - reflexivity.
  - simpl.
    unfold step, step_row.
    remember (start + 1)%Z as s eqn:Hs.
    replace (start + 2)%Z with (s + 1)%Z by (subst s; lia).
    replace (start + 3)%Z with (s + 2)%Z by (subst s; lia).
    replace (step r (start + 1)) with (step r s) by (subst s; reflexivity).
    f_equal.
    + subst s.
      replace (start + 1 - 1)%Z with start by lia.
      reflexivity.
    + replace (s + 1 + 1)%Z with (s + 2)%Z by lia.
      change
        (rule30_window_from (r s) (r (s + 1))
           (map r (z_segment (s + 2) len)) =
         map (step r) (z_segment (s + 1) len)).
      exact (IH s).
Qed.

Lemma rule30_window_on_segment :
  forall r start len,
    rule30_window (map r (z_segment start (S (S len)))) =
    map (step r) (z_segment (start + 1) len).
Proof.
  intros r start len.
  simpl.
  replace (start + 1 + 1)%Z with (start + 2)%Z by lia.
  exact (rule30_window_from_on_segment r start len).
Qed.

Lemma rule30_window_on_centered_carrier :
  forall R u,
    rule30_window (predecessor_carrier_window R u) =
    row_window (step u) R.
Proof.
  intros R u.
  unfold predecessor_carrier_window, row_window, centered_coords.
  replace (S (2 * S R)) with (S (S (S (2 * R)))) by lia.
  replace (- Z.of_nat R)%Z with (- Z.of_nat (S R) + 1)%Z by lia.
  exact (rule30_window_on_segment u (- Z.of_nat (S R)) (S (2 * R))).
Qed.

Lemma cutoff_predecessor_carrier_length :
  forall R T P m,
    length (cutoff_predecessor_carrier R T P m) = predecessor_carrier_length R.
Proof.
  intros R T P m.
  unfold cutoff_predecessor_carrier.
  apply predecessor_carrier_window_length.
Qed.

Lemma nth_error_z_segment :
  forall start len i,
    (i < len)%nat ->
    nth_error (z_segment start len) i = Some (start + Z.of_nat i).
Proof.
  intros start len.
  revert start.
  induction len as [|len IH]; intros start i Hi.
  - lia.
  - destruct i as [|i].
    + simpl.
      replace (Z.of_nat 0%nat) with 0%Z by reflexivity.
      rewrite Z.add_0_r.
      reflexivity.
    + simpl.
      rewrite (IH (start + 1)%Z i).
      * f_equal.
        lia.
      * lia.
Qed.

Lemma centered_coords_in_bounds :
  forall radius x,
    In x (centered_coords radius) ->
    (- Z.of_nat radius <= x <= Z.of_nat radius)%Z.
Proof.
  intros radius x Hin.
  unfold centered_coords in Hin.
  pose proof (z_segment_in_bounds (- Z.of_nat radius) (S (2 * radius)) x Hin)
    as Hbounds.
  lia.
Qed.

Lemma centered_coords_lookup :
  forall radius x,
    (- Z.of_nat radius <= x <= Z.of_nat radius)%Z ->
    exists i,
      nth_error (centered_coords radius) i = Some x.
Proof.
  intros radius x Hx.
  set (i := Z.to_nat (x + Z.of_nat radius)).
  exists i.
  assert (Hnonneg : (0 <= x + Z.of_nat radius)%Z) by lia.
  assert (Hi : (i < S (2 * radius))%nat).
  { unfold i.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by exact Hnonneg.
    lia. }
  unfold centered_coords.
  rewrite (nth_error_z_segment (- Z.of_nat radius) (S (2 * radius)) i Hi).
  f_equal.
  unfold i.
  rewrite Z2Nat.id by exact Hnonneg.
  lia.
Qed.

Lemma nth_error_row_window_from_coords :
  forall r radius i x,
    nth_error (centered_coords radius) i = Some x ->
    nth_error (row_window r radius) i = Some (r x).
Proof.
  intros r radius i x Hcoord.
  unfold row_window.
  exact (nth_error_map_some Z bit r (centered_coords radius) i x Hcoord).
Qed.

Lemma row_window_eq_implies_same_on_interval :
  forall radius u v,
    row_window u radius = row_window v radius ->
    same_on_interval u v 0%Z radius.
Proof.
  intros radius u v Hwindow y Hy.
  unfold in_interval in Hy.
  destruct (centered_coords_lookup radius y Hy) as [i Hi].
  apply (f_equal (fun l => nth_error l i)) in Hwindow.
  rewrite (nth_error_row_window_from_coords u radius i y Hi) in Hwindow.
  rewrite (nth_error_row_window_from_coords v radius i y Hi) in Hwindow.
  inversion Hwindow.
  reflexivity.
Qed.

Lemma same_on_interval_implies_row_window_eq :
  forall radius u v,
    same_on_interval u v 0%Z radius ->
    row_window u radius = row_window v radius.
Proof.
  intros radius u v Hagree.
  unfold row_window.
  apply map_ext_in.
  intros x Hx.
  apply Hagree.
  apply centered_coords_in_bounds.
  exact Hx.
Qed.

Lemma iter_row_plus :
  forall a b r,
    iter_row (a + b) r = iter_row a (iter_row b r).
Proof.
  induction a as [|a IH]; intros b r.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Lemma canonical_row_after :
  forall t s,
    canonical_row (t + s)%nat = iter_row s (canonical_row t).
Proof.
  intros t s.
  rewrite !canonical_row_as_iter.
  replace (t + s)%nat with (s + t)%nat by lia.
  apply iter_row_plus.
Qed.

Lemma row_window_canonical_row :
  forall radius t,
    row_window (canonical_row t) radius = center_window radius t.
Proof.
  intros radius t.
  unfold row_window, center_window.
  reflexivity.
Qed.

Lemma row_window_step_canonical_row :
  forall radius t,
    row_window (step (canonical_row t)) radius =
    center_window radius (S t).
Proof.
  intros radius t.
  rewrite <- canonical_row_step.
  apply row_window_canonical_row.
Qed.

Lemma center_window_eq_weaken :
  forall n m t u,
    (m <= n)%nat ->
    center_window n t = center_window n u ->
    center_window m t = center_window m u.
Proof.
  intros n m t u Hmn Heq.
  rewrite <- (row_window_canonical_row n t) in Heq.
  rewrite <- (row_window_canonical_row n u) in Heq.
  apply row_window_eq_implies_same_on_interval in Heq.
  rewrite <- (row_window_canonical_row m t).
  rewrite <- (row_window_canonical_row m u).
  apply same_on_interval_implies_row_window_eq.
  eapply same_on_interval_weaken.
  - exact Hmn.
  - exact Heq.
Qed.

Theorem center_window_repeat_transports_forward :
  forall radius steps a b,
    center_window (radius + steps) a = center_window (radius + steps) b ->
    center_window radius (a + steps)%nat =
    center_window radius (b + steps)%nat.
Proof.
  intros radius steps a b Heq.
  rewrite <- (row_window_canonical_row (radius + steps) a) in Heq.
  rewrite <- (row_window_canonical_row (radius + steps) b) in Heq.
  apply row_window_eq_implies_same_on_interval in Heq.
  rewrite <- (row_window_canonical_row radius (a + steps)%nat).
  rewrite <- (row_window_canonical_row radius (b + steps)%nat).
  apply same_on_interval_implies_row_window_eq.
  intros y Hy.
  rewrite canonical_row_after.
  rewrite canonical_row_after.
  apply iter_row_locality.
  intros z Hz.
  apply Heq.
  unfold in_interval in *.
  lia.
Qed.

Theorem center_window_repeat_transports_forward_block :
  forall radius extra a b s,
    (s <= extra)%nat ->
    center_window (radius + extra) a = center_window (radius + extra) b ->
    center_window radius (a + s)%nat =
    center_window radius (b + s)%nat.
Proof.
  intros radius extra a b s Hs Heq.
  apply center_window_repeat_transports_forward.
  apply center_window_eq_weaken with (n := (radius + extra)%nat).
  - lia.
  - exact Heq.
Qed.

Lemma cutoff_predecessor_successor_time :
  forall T P m,
    (0 < P)%nat ->
    S (T + m * P + (P - 1)) = (T + (S m) * P)%nat.
Proof.
  intros T P m HP.
  lia.
Qed.

Lemma eventual_periodicity_freezes_cutoff_phase :
  forall n T P,
    (0 < P)%nat ->
    (forall t,
      center_window n (T + t + P)%nat =
      center_window n (T + t)%nat) ->
    forall m,
      center_window n (T + m * P)%nat = center_window n T.
Proof.
  intros n T P HP Hperiod.
  induction m as [|m IH].
  - simpl.
    rewrite Nat.add_0_r.
    reflexivity.
  - replace (center_window n (T + S m * P)%nat)
      with (center_window n ((T + m * P) + P)%nat).
    rewrite (Hperiod (m * P)%nat).
    exact IH.
    f_equal.
    lia.
Qed.

Theorem cutoff_predecessor_realizes_cutoff_target_window :
  forall n T P m,
    (0 < P)%nat ->
    (forall t,
      center_window n (T + t + P)%nat =
      center_window n (T + t)%nat) ->
    local_target_window_realization n (canonical_row T)
      (cutoff_predecessor T P m).
Proof.
  intros n T P m HP Hperiod.
  unfold local_target_window_realization, cutoff_predecessor.
  rewrite row_window_step_canonical_row.
  rewrite (cutoff_predecessor_successor_time T P m HP).
  rewrite (eventual_periodicity_freezes_cutoff_phase n T P HP Hperiod (S m)).
  apply row_window_canonical_row.
Qed.

Theorem eventual_periodicity_yields_repeated_cutoff_predecessors :
  forall n,
    eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        local_target_window_realization n (canonical_row T)
          (cutoff_predecessor T P m).
Proof.
  intros n [T [P [HP Hperiod]]].
  exists T, P.
  split.
  - exact HP.
  - intro m.
    exact
      (cutoff_predecessor_realizes_cutoff_target_window n T P m HP Hperiod).
Qed.

Lemma finite_periodic_orbit_tail_trim :
  forall n T P K,
    finite_periodic_orbit n T P (S K) ->
    finite_periodic_orbit n T P K.
Proof.
  intros n T P K [HP Horbit].
  split.
  - exact HP.
  - intros m Hm.
    exact (Horbit m (Nat.le_trans _ _ _ Hm (Nat.le_succ_diag_r K))).
Qed.

Lemma finite_periodic_orbit_successor_step :
  forall n T P K m,
    finite_periodic_orbit n T P (S K) ->
    (m <= K)%nat ->
    center_window n (T + (S m) * P)%nat = center_window n T.
Proof.
  intros n T P K m [HP Horbit] Hm.
  apply Horbit.
  lia.
Qed.

Theorem eventual_periodicity_implies_finite_periodic_orbit :
  forall n,
    eventually_periodic_center_window n ->
    forall K,
      exists T P,
        finite_periodic_orbit n T P K.
Proof.
  intros n [T [P [HP Hperiod]]] K.
  exists T, P.
  split.
  - exact HP.
  - intros m Hm.
    exact (eventual_periodicity_freezes_cutoff_phase n T P HP Hperiod m).
Qed.

Theorem cutoff_predecessor_realizes_cutoff_target_window_from_finite_orbit :
  forall n T P K m,
    finite_periodic_orbit n T P (S K) ->
    (m <= K)%nat ->
    local_target_window_realization n (canonical_row T)
      (cutoff_predecessor T P m).
Proof.
  intros n T P K m Horbit Hm.
  destruct Horbit as [HP Horbit].
  unfold local_target_window_realization, cutoff_predecessor.
  rewrite row_window_step_canonical_row.
  rewrite (cutoff_predecessor_successor_time T P m HP).
  rewrite (finite_periodic_orbit_successor_step n T P K m).
  - apply row_window_canonical_row.
  - split.
    + exact HP.
    + exact Horbit.
  - exact Hm.
Qed.

Theorem eventual_periodicity_yields_cutoff_predecessor_carrier_orbit :
  forall n,
    eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        local_target_window_realization n (canonical_row T)
          (cutoff_predecessor T P m) /\
        length (cutoff_predecessor_carrier n T P m) =
          predecessor_carrier_length n.
Proof.
  intros n Heventual.
  destruct (eventual_periodicity_yields_repeated_cutoff_predecessors n Heventual)
    as [T [P [HP Hpred]]].
  exists T, P.
  split.
  - exact HP.
  - intro m.
    split.
    + exact (Hpred m).
    + apply cutoff_predecessor_carrier_length.
Qed.

Theorem cutoff_predecessor_carrier_realizes_cutoff_window :
  forall R T P m,
    (0 < P)%nat ->
    (forall t,
      center_window R (T + t + P)%nat =
      center_window R (T + t)%nat) ->
    carrier_realizes_window R (canonical_cutoff_window R T)
      (cutoff_predecessor_carrier R T P m).
Proof.
  intros R T P m HP Hperiod.
  split.
  - apply cutoff_predecessor_carrier_length.
  - unfold canonical_cutoff_window, cutoff_predecessor_carrier.
    rewrite rule30_window_on_centered_carrier.
    unfold predecessor_carrier_window, row_window.
    exact
      (cutoff_predecessor_realizes_cutoff_target_window R T P m HP Hperiod).
Qed.

Theorem eventual_periodicity_yields_carrier_memory_orbit :
  forall n,
    eventually_periodic_center_window n ->
    exists T P,
      (0 < P)%nat /\
      forall m,
        carrier_realizes_window n (canonical_cutoff_window n T)
          (cutoff_predecessor_carrier n T P m).
Proof.
  intros n Heventual.
  destruct Heventual as [T [P [HP Hperiod]]].
  exists T, P.
  split.
  - exact HP.
  - intro m.
    exact
      (cutoff_predecessor_carrier_realizes_cutoff_window n T P m HP Hperiod).
Qed.

Theorem finite_periodic_orbit_implies_finite_carrier_memory_orbit :
  forall n T P K,
    finite_periodic_orbit n T P (S K) ->
    finite_carrier_memory_orbit n T P K.
Proof.
  intros n T P K Horbit m Hm.
  split.
  - apply cutoff_predecessor_carrier_length.
  - unfold canonical_cutoff_window, cutoff_predecessor_carrier.
    rewrite rule30_window_on_centered_carrier.
    transitivity (row_window (canonical_row T) n).
    + exact
        (cutoff_predecessor_realizes_cutoff_target_window_from_finite_orbit
          n T P K m Horbit Hm).
    + apply row_window_canonical_row.
Qed.

Lemma cutoff_predecessor_at_successor_cutoff :
  forall T P m,
    (0 < P)%nat ->
    cutoff_predecessor (S T) P m =
    canonical_row (T + (S m) * P)%nat.
Proof.
  intros T P m HP.
  unfold cutoff_predecessor.
  f_equal.
  lia.
Qed.

Theorem finite_periodic_orbit_transports_backward_one_step :
  forall n T P K,
    finite_periodic_orbit n (S T) P (S K) ->
    backward_transport_carrier_orbit n T P K.
Proof.
  intros n T P K Horbit m Hm.
  pose proof
    (finite_periodic_orbit_implies_finite_carrier_memory_orbit
      n (S T) P K Horbit m Hm) as Hcarrier.
  unfold backward_transport_carrier_orbit.
  unfold finite_carrier_memory_orbit in Hcarrier.
  unfold carrier_realizes_window, canonical_cutoff_window,
    cutoff_predecessor_carrier in *.
  destruct Horbit as [HP _].
  rewrite (cutoff_predecessor_at_successor_cutoff T P m HP) in Hcarrier.
  exact Hcarrier.
Qed.

Theorem equal_cutoff_predecessor_carriers_at_successor_cutoff_transport_backward :
  forall R T P i j,
    (0 < P)%nat ->
    cutoff_predecessor_carrier R (S T) P i =
    cutoff_predecessor_carrier R (S T) P j ->
    center_window (S R) (T + (S i) * P)%nat =
    center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P i j HP Heq.
  unfold cutoff_predecessor_carrier, predecessor_carrier_window in Heq.
  rewrite (cutoff_predecessor_at_successor_cutoff T P i HP) in Heq.
  rewrite (cutoff_predecessor_at_successor_cutoff T P j HP) in Heq.
  repeat rewrite row_window_canonical_row in Heq.
  exact Heq.
Qed.

Theorem repeated_cutoff_predecessor_carrier_at_successor_cutoff_transports_backward :
  forall R T P K,
    (0 < P)%nat ->
    repeated_cutoff_predecessor_carrier R (S T) P K ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P K HP [i [j [Hij [Hj Heq]]]].
  exists i, j.
  repeat split; try exact Hij; try exact Hj.
  exact
    (equal_cutoff_predecessor_carriers_at_successor_cutoff_transport_backward
      R T P i j HP Heq).
Qed.

Theorem finite_periodic_orbit_plus_repeated_carrier_transports_backward :
  forall R T P K,
    finite_periodic_orbit R (S T) P (S K) ->
    repeated_cutoff_predecessor_carrier R (S T) P K ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P K Horbit Hrepeat.
  destruct Horbit as [HP _].
  exact
    (repeated_cutoff_predecessor_carrier_at_successor_cutoff_transports_backward
      R T P K HP Hrepeat).
Qed.

Theorem long_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (length (carrier_pool R) < S K)%nat ->
    finite_carrier_memory_orbit R T P K ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  set (xs := seq 0 (S K)).
  assert (Hnodup : NoDup xs).
  { unfold xs.
    apply seq_NoDup. }
  assert (Hcat :
      forall m, In m xs -> In (cutoff_predecessor_carrier R T P m) (carrier_pool R)).
  { intros m Hm.
    unfold xs in Hm.
    apply in_seq in Hm.
    destruct Hm as [_ Hm].
    apply carrier_pool_complete.
    destruct (Horbit m) as [Hlen _].
    - lia.
    - exact Hlen. }
  assert (Hlen : (length (carrier_pool R) < length xs)%nat).
  { unfold xs.
    rewrite length_seq.
    exact Hbound. }
  destruct
    (pigeonhole_typed nat (list bit) (list_eq_dec Bool.bool_dec)
      (cutoff_predecessor_carrier R T P) xs (carrier_pool R)
      Hnodup Hcat Hlen)
    as [i [j [Hi [Hj [Hij Heq]]]]].
  unfold xs in Hi, Hj.
  apply in_seq in Hi.
  apply in_seq in Hj.
  destruct Hi as [_ Hi].
  destruct Hj as [_ Hj].
  destruct (Nat.lt_total i j) as [Hlt | [Heqij | Hgt]].
  - exists i, j.
    repeat split; try exact Hlt; try lia.
    exact Heq.
  - exfalso.
    apply Hij.
    exact Heqij.
  - exists j, i.
    repeat split; try exact Hgt; try lia.
    symmetry.
    exact Heq.
Qed.

Theorem long_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (length (carrier_pool R) < S K)%nat ->
    finite_periodic_orbit R T P (S K) ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  apply long_finite_carrier_memory_orbit_has_repeated_carrier with (T := T).
  - exact Hbound.
  - exact (finite_periodic_orbit_implies_finite_carrier_memory_orbit R T P K Horbit).
Qed.

Theorem long_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (length (carrier_pool R) < S K)%nat ->
    finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P K Hbound Horbit.
  apply finite_periodic_orbit_plus_repeated_carrier_transports_backward
    with (R := R) (T := T) (P := P) (K := K).
  - exact Horbit.
  - apply long_finite_periodic_orbit_has_repeated_carrier.
    + exact Hbound.
    + exact Horbit.
Qed.

Theorem large_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (predecessor_carrier_length R) < S K)%nat ->
    finite_carrier_memory_orbit R T P K ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  apply long_finite_carrier_memory_orbit_has_repeated_carrier.
  - rewrite carrier_pool_length.
    exact Hbound.
  - exact Horbit.
Qed.

Theorem large_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (Nat.pow 2 (predecessor_carrier_length R) < S K)%nat ->
    finite_periodic_orbit R T P (S K) ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  apply long_finite_periodic_orbit_has_repeated_carrier.
  - rewrite carrier_pool_length.
    exact Hbound.
  - exact Horbit.
Qed.

Theorem large_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (Nat.pow 2 (predecessor_carrier_length R) < S K)%nat ->
    finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P K Hbound Horbit.
  apply long_finite_periodic_orbit_transports_backward.
  - rewrite carrier_pool_length.
    exact Hbound.
  - exact Horbit.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_backward_repeat :
  forall R T P,
    (0 < P)%nat ->
    (forall t,
      center_window R (S T + t + P)%nat =
      center_window R (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= Nat.pow 2 (predecessor_carrier_length R))%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P HP Hperiod.
  set (K := Nat.pow 2 (predecessor_carrier_length R)).
  assert (Hbound : (Nat.pow 2 (predecessor_carrier_length R) < S K)%nat).
  { unfold K.
    lia. }
  assert (Horbit : finite_periodic_orbit R (S T) P (S K)).
  { split.
    - exact HP.
    - intros m Hm.
      exact
        (eventual_periodicity_freezes_cutoff_phase
          R (S T) P HP Hperiod m). }
  destruct
    (large_finite_periodic_orbit_transports_backward R T P K Hbound Horbit)
    as [i [j [Hij [Hj Heq]]]].
  exists i, j.
  repeat split; try exact Hij; try exact Heq.
  unfold K in Hj.
  exact Hj.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_backward_repeat_block :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= Nat.pow 2 (predecessor_carrier_length (R + extra)))%nat /\
      forall s,
        (s <= extra)%nat ->
        center_window (S R) (T + (S i) * P + s)%nat =
        center_window (S R) (T + (S j) * P + s)%nat.
Proof.
  intros R T P extra HP Hperiod.
  destruct
    (periodic_tail_at_successor_cutoff_has_backward_repeat
      (R + extra) T P HP Hperiod)
    as [i [j [Hij [Hj Heq]]]].
  exists i, j.
  split.
  - exact Hij.
  - split.
    + exact Hj.
    + intros s Hs.
      replace (S R + extra)%nat with (S (R + extra)) in Heq by lia.
      exact
        (center_window_repeat_transports_forward_block
          (S R) extra
          (T + (S i) * P)%nat
          (T + (S j) * P)%nat
          s Hs Heq).
Qed.

Theorem predecessor_carrier_window_determines_target_window :
  forall R u v,
    predecessor_carrier_window R u =
    predecessor_carrier_window R v ->
    row_window (step u) R = row_window (step v) R.
Proof.
  intros R u v Hcarrier.
  apply same_on_interval_implies_row_window_eq.
  apply step_row_locality.
  apply row_window_eq_implies_same_on_interval.
  exact Hcarrier.
Qed.

Theorem local_target_window_realization_iff_rule30_window :
  forall R target u,
    local_target_window_realization R target u <->
    rule30_window (predecessor_carrier_window R u) = row_window target R.
Proof.
  intros R target u.
  unfold local_target_window_realization.
  rewrite rule30_window_on_centered_carrier.
  tauto.
Qed.

Theorem local_target_window_realization_respects_predecessor_carrier :
  forall R target u v,
    predecessor_carrier_window R u =
    predecessor_carrier_window R v ->
    local_target_window_realization R target u ->
    local_target_window_realization R target v.
Proof.
  intros R target u v Hcarrier Hreal.
  unfold local_target_window_realization in *.
  pose proof
    (predecessor_carrier_window_determines_target_window R u v Hcarrier)
    as Hstep.
  rewrite Hreal in Hstep.
  symmetry.
  exact Hstep.
Qed.

Lemma boundary_signature_pool_length :
  length boundary_signature_pool = 4%nat.
Proof.
  reflexivity.
Qed.

Lemma boundary_signature_pool_NoDup :
  NoDup boundary_signature_pool.
Proof.
  unfold boundary_signature_pool.
  constructor.
  - simpl.
    intros [Hin | [Hin | [Hin | []]]].
    + discriminate Hin.
    + discriminate Hin.
    + discriminate Hin.
  - constructor.
    + simpl.
      intros [Hin | [Hin | []]].
      * discriminate Hin.
      * discriminate Hin.
    + constructor.
      * simpl.
        intros [Hin | []].
        discriminate Hin.
      * constructor.
        -- simpl.
           intros [].
        -- constructor.
Qed.

Lemma carrier_right_boundary_signature_in_pool :
  forall carrier,
    In (carrier_right_boundary_signature carrier) boundary_signature_pool.
Proof.
  intro carrier.
  destruct (carrier_right_boundary_signature carrier) as [b c].
  destruct b, c; simpl; auto.
Qed.

Lemma long_carrier_has_right_boundary_signature :
  forall carrier,
    (2 <= length carrier)%nat ->
    exists b c rest,
      carrier_right_boundary_signature carrier = (b, c) /\
      rev carrier = c :: b :: rest.
Proof.
  intros carrier Hlen.
  unfold carrier_right_boundary_signature.
  destruct (rev carrier) as [|c rev_carrier] eqn:Hrev.
  - rewrite <- length_rev in Hlen.
    rewrite Hrev in Hlen.
    simpl in Hlen.
    lia.
  - destruct rev_carrier as [|b rest] eqn:Hrev_carrier.
    + rewrite <- length_rev in Hlen.
      rewrite Hrev in Hlen.
      simpl in Hlen.
      lia.
    + exists b, c, rest.
      split; reflexivity.
Qed.

Lemma predecessor_carrier_window_has_right_boundary_signature :
  forall R u,
    exists b c rest,
      carrier_right_boundary_signature (predecessor_carrier_window R u) = (b, c) /\
      rev (predecessor_carrier_window R u) = c :: b :: rest.
Proof.
  intros R u.
  apply long_carrier_has_right_boundary_signature.
  rewrite (predecessor_carrier_window_length R u).
  unfold predecessor_carrier_length.
  lia.
Qed.

Theorem local_target_window_realization_determined_by_boundary_signature :
  forall R target u v,
    local_target_window_realization R target u ->
    local_target_window_realization R target v ->
    carrier_right_boundary_signature (predecessor_carrier_window R u) =
    carrier_right_boundary_signature (predecessor_carrier_window R v) ->
    predecessor_carrier_window R u = predecessor_carrier_window R v.
Proof.
  intros R target u v Hu Hv Hsig.
  destruct
    (predecessor_carrier_window_has_right_boundary_signature R u)
    as [b [c [rest_u [Hsig_u Hrev_u]]]].
  destruct
    (predecessor_carrier_window_has_right_boundary_signature R v)
    as [b' [c' [rest_v [Hsig_v Hrev_v]]]].
  rewrite Hsig_u in Hsig.
  rewrite Hsig_v in Hsig.
  inversion Hsig; subst b' c'.
  assert (Hu_rev :
      rule30_window_rev (rev (predecessor_carrier_window R u)) =
      rev (row_window target R)).
  { rewrite rule30_window_rev_on_centered_carrier.
    unfold local_target_window_realization in Hu.
    rewrite Hu.
    reflexivity. }
  assert (Hv_rev :
      rule30_window_rev (rev (predecessor_carrier_window R v)) =
      rev (row_window target R)).
  { rewrite rule30_window_rev_on_centered_carrier.
    unfold local_target_window_realization in Hv.
    rewrite Hv.
    reflexivity. }
  rewrite Hrev_u in Hu_rev.
  rewrite Hrev_v in Hv_rev.
  assert (Hrev_eq :
      rev (predecessor_carrier_window R u) =
      rev (predecessor_carrier_window R v)).
  { rewrite Hrev_u.
    rewrite Hrev_v.
    transitivity
      (reconstruct_carrier_rev_from (rev (row_window target R)) b c).
    - exact
        (rule30_window_rev_determined_by_boundary
          (rev (row_window target R)) b c rest_u Hu_rev).
    - symmetry.
      exact
        (rule30_window_rev_determined_by_boundary
          (rev (row_window target R)) b c rest_v Hv_rev).
  }
  apply (f_equal (@rev bit)) in Hrev_eq.
  repeat rewrite rev_involutive in Hrev_eq.
  exact Hrev_eq.
Qed.

Definition cutoff_predecessor_boundary_signature
    (R T P m : nat) : bit * bit :=
  carrier_right_boundary_signature (cutoff_predecessor_carrier R T P m).

Definition repeated_cutoff_predecessor_boundary_signature
    (R T P K : nat) : Prop :=
  exists i j,
    (i < j)%nat /\
    (j <= K)%nat /\
    cutoff_predecessor_boundary_signature R T P i =
    cutoff_predecessor_boundary_signature R T P j.

Theorem long_finite_carrier_memory_orbit_has_repeated_boundary_signature :
  forall R T P K,
    (length boundary_signature_pool < S K)%nat ->
    finite_carrier_memory_orbit R T P K ->
    repeated_cutoff_predecessor_boundary_signature R T P K.
Proof.
  intros R T P K Hbound Horbit.
  set (xs := seq 0 (S K)).
  assert (Hnodup : NoDup xs).
  { unfold xs.
    apply seq_NoDup. }
  assert (Hcat :
      forall m, In m xs ->
        In (cutoff_predecessor_boundary_signature R T P m)
           boundary_signature_pool).
  { intros m Hm.
    apply carrier_right_boundary_signature_in_pool. }
  assert (Hlen : (length boundary_signature_pool < length xs)%nat).
  { unfold xs.
    rewrite length_seq.
    exact Hbound. }
  destruct
    (pigeonhole_typed nat (bit * bit) bit_pair_eq_dec
      (cutoff_predecessor_boundary_signature R T P)
      xs boundary_signature_pool Hnodup Hcat Hlen)
    as [i [j [Hi [Hj [Hij Hsig]]]]].
  unfold xs in Hi, Hj.
  apply in_seq in Hi.
  apply in_seq in Hj.
  destruct Hi as [_ Hi].
  destruct Hj as [_ Hj].
  destruct (Nat.lt_total i j) as [Hlt | [Heqij | Hgt]].
  - exists i, j.
    repeat split; try exact Hlt; try lia.
    exact Hsig.
  - exfalso.
    apply Hij.
    exact Heqij.
  - exists j, i.
    repeat split; try exact Hgt; try lia.
    symmetry.
    exact Hsig.
Qed.

Theorem repeated_boundary_signature_implies_repeated_carrier :
  forall R T P K,
    finite_carrier_memory_orbit R T P K ->
    repeated_cutoff_predecessor_boundary_signature R T P K ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Horbit [i [j [Hij [Hj Hsig]]]].
  assert (Hi : (i <= K)%nat) by lia.
  destruct (Horbit i Hi) as [_ Hcarrier_i].
  destruct (Horbit j Hj) as [_ Hcarrier_j].
  assert (Hreal_i :
      local_target_window_realization R (canonical_row T)
        (cutoff_predecessor T P i)).
  { apply
      (proj2
        (local_target_window_realization_iff_rule30_window
          R (canonical_row T) (cutoff_predecessor T P i))).
    unfold canonical_cutoff_window in Hcarrier_i.
    rewrite <- row_window_canonical_row in Hcarrier_i.
    exact Hcarrier_i. }
  assert (Hreal_j :
      local_target_window_realization R (canonical_row T)
        (cutoff_predecessor T P j)).
  { apply
      (proj2
        (local_target_window_realization_iff_rule30_window
          R (canonical_row T) (cutoff_predecessor T P j))).
    unfold canonical_cutoff_window in Hcarrier_j.
    rewrite <- row_window_canonical_row in Hcarrier_j.
    exact Hcarrier_j. }
  exists i, j.
  repeat split; try exact Hij; try exact Hj.
  exact
    (local_target_window_realization_determined_by_boundary_signature
      R (canonical_row T)
      (cutoff_predecessor T P i)
      (cutoff_predecessor T P j)
      Hreal_i Hreal_j Hsig).
Qed.

Theorem small_finite_carrier_memory_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    finite_carrier_memory_orbit R T P K ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  apply repeated_boundary_signature_implies_repeated_carrier with (K := K).
  - exact Horbit.
  - apply long_finite_carrier_memory_orbit_has_repeated_boundary_signature.
    + rewrite boundary_signature_pool_length.
      exact Hbound.
    + exact Horbit.
Qed.

Theorem small_finite_periodic_orbit_has_repeated_carrier :
  forall R T P K,
    (4 < S K)%nat ->
    finite_periodic_orbit R T P (S K) ->
    repeated_cutoff_predecessor_carrier R T P K.
Proof.
  intros R T P K Hbound Horbit.
  apply small_finite_carrier_memory_orbit_has_repeated_carrier.
  - exact Hbound.
  - exact
      (finite_periodic_orbit_implies_finite_carrier_memory_orbit
        R T P K Horbit).
Qed.

Theorem small_finite_periodic_orbit_transports_backward :
  forall R T P K,
    (4 < S K)%nat ->
    finite_periodic_orbit R (S T) P (S K) ->
    exists i j,
      (i < j)%nat /\
      (j <= K)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P K Hbound Horbit.
  apply finite_periodic_orbit_plus_repeated_carrier_transports_backward
    with (R := R) (T := T) (P := P) (K := K).
  - exact Horbit.
  - apply small_finite_periodic_orbit_has_repeated_carrier.
    + exact Hbound.
    + exact Horbit.
Qed.

Definition small_backward_pair_pool : list (nat * nat) :=
  flat_map
    (fun i => map (fun d => (i, (i + S d)%nat)) (seq 0 (4 - i)%nat))
    (seq 0 4%nat).

Lemma small_backward_pair_pool_complete :
  forall i j,
    (i < j)%nat ->
    (j <= 4)%nat ->
    In (i, j) small_backward_pair_pool.
Proof.
  intros i j Hij Hj.
  unfold small_backward_pair_pool.
  apply in_flat_map.
  exists i.
  split.
  - apply in_seq.
    lia.
  - apply in_map_iff.
    exists (j - i - 1)%nat.
    split.
    + f_equal.
      lia.
    + apply in_seq.
      lia.
Qed.

Lemma small_backward_pair_pool_sound :
  forall i j,
    In (i, j) small_backward_pair_pool ->
    (i < j)%nat /\ (j <= 4)%nat.
Proof.
  intros i j Hin.
  unfold small_backward_pair_pool in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [i0 [Hi0 Hpair]].
  apply in_seq in Hi0.
  destruct Hi0 as [Hi0lo Hi0hi].
  apply in_map_iff in Hpair.
  destruct Hpair as [d [Hd_eq Hd_in]].
  inversion Hd_eq; subst i0.
  apply in_seq in Hd_in.
  destruct Hd_in as [Hdlo Hdhi].
  split.
  - lia.
  - lia.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_small_backward_repeat :
  forall R T P,
    (0 < P)%nat ->
    (forall t,
      center_window R (S T + t + P)%nat =
      center_window R (S T + t)%nat) ->
    exists i j,
      (i < j)%nat /\
      (j <= 4)%nat /\
      center_window (S R) (T + (S i) * P)%nat =
      center_window (S R) (T + (S j) * P)%nat.
Proof.
  intros R T P HP Hperiod.
  set (K := 4%nat).
  assert (Hbound : (4 < S K)%nat).
  { unfold K.
    lia. }
  assert (Horbit : finite_periodic_orbit R (S T) P (S K)).
  { split.
    - exact HP.
    - intros m Hm.
      exact
        (eventual_periodicity_freezes_cutoff_phase
          R (S T) P HP Hperiod m). }
  destruct
    (small_finite_periodic_orbit_transports_backward
      R T P K Hbound Horbit)
    as [i [j [Hij [Hj Heq]]]].
  exists i, j.
  repeat split; try exact Hij; try exact Heq.
  unfold K in Hj.
  exact Hj.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_small_backward_repeat_block :
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
        center_window (S R) (T + (S j) * P + s)%nat.
Proof.
  intros R T P extra HP Hperiod.
  destruct
    (periodic_tail_at_successor_cutoff_has_small_backward_repeat
      (R + extra) T P HP Hperiod)
    as [i [j [Hij [Hj Heq]]]].
  exists i, j.
  split.
  - exact Hij.
  - split.
    + exact Hj.
    + intros s Hs.
      replace (S R + extra)%nat with (S (R + extra)) in Heq by lia.
      exact
        (center_window_repeat_transports_forward_block
          (S R) extra
          (T + (S i) * P)%nat
          (T + (S j) * P)%nat
          s Hs Heq).
Qed.

Theorem periodic_tail_at_successor_cutoff_has_small_backward_pair_from_pool :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists ij,
      In ij small_backward_pair_pool /\
      small_backward_pair_block R T P extra ij.
Proof.
  intros R T P extra HP Hperiod.
  destruct
    (periodic_tail_at_successor_cutoff_has_small_backward_repeat_block
      R T P extra HP Hperiod)
    as [i [j [Hij [Hj Hblock]]]].
  exists (i, j).
  split.
  - exact (small_backward_pair_pool_complete i j Hij Hj).
  - repeat split; try exact Hij; try exact Hj; exact Hblock.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_unbounded_small_backward_pair :
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
          small_backward_pair_block R T P extra (i, j).
Proof.
  intros R T P HP Hperiod.
  assert (Hall :
      forall N,
        exists ij,
          In ij small_backward_pair_pool /\
          exists extra,
            (N <= extra)%nat /\
            small_backward_pair_block R T P extra ij).
  { intro N.
    destruct
      (periodic_tail_at_successor_cutoff_has_small_backward_pair_from_pool
        R T P N HP (Hperiod N))
      as [ij [Hij HQ]].
    exists ij.
    split.
    - exact Hij.
    - exists N.
      split.
      + lia.
      + exact HQ.
  }
  destruct
    (finite_list_has_arbitrarily_often_member
      (nat * nat) small_backward_pair_pool
      (fun ij extra => small_backward_pair_block R T P extra ij) Hall)
    as [ij [Hij Hfar]].
  destruct ij as [i j].
  exists i, j.
  split.
  - exact Hij.
  - exact Hfar.
Qed.

Theorem small_backward_repeat_block_yields_finite_repeat_block :
  forall n T P extra i j,
    (0 < P)%nat ->
    (i < j)%nat ->
    (forall s,
      (s <= extra)%nat ->
      center_window n (T + (S i) * P + s)%nat =
      center_window n (T + (S j) * P + s)%nat) ->
    finite_repeat_block n (T + (S i) * P)%nat ((j - i) * P) extra.
Proof.
  intros n T P extra i j HP Hij Hblock.
  split.
  - apply Nat.mul_pos_pos; lia.
  - intros s Hs.
    specialize (Hblock s Hs).
    replace ((T + (S i) * P + (j - i) * P + s)%nat)
      with (T + (S j) * P + s)%nat by lia.
    symmetry.
    exact Hblock.
Qed.

Theorem periodic_tail_at_successor_cutoff_has_small_backward_finite_repeat_block :
  forall R T P extra,
    (0 < P)%nat ->
    (forall t,
      center_window (R + extra) (S T + t + P)%nat =
      center_window (R + extra) (S T + t)%nat) ->
    exists T' P',
      (T + P <= T')%nat /\
      (T' <= T + 4 * P)%nat /\
      (P' <= 4 * P)%nat /\
      finite_repeat_block (S R) T' P' extra.
Proof.
  intros R T P extra HP Hperiod.
  destruct
    (periodic_tail_at_successor_cutoff_has_small_backward_repeat_block
      R T P extra HP Hperiod)
    as [i [j [Hij [Hj Hblock]]]].
  exists (T + (S i) * P)%nat, ((j - i) * P)%nat.
  split.
  - lia.
  - split.
    + assert (Hi4 : (S i <= 4)%nat) by lia.
      apply Nat.add_le_mono_l.
      apply Nat.mul_le_mono_nonneg_r.
      * lia.
      * exact Hi4.
    + split.
      * assert (Hij4 : (j - i <= 4)%nat) by lia.
        apply Nat.mul_le_mono_nonneg_r.
        -- lia.
        -- exact Hij4.
      * apply
          (small_backward_repeat_block_yields_finite_repeat_block
            (S R) T P extra i j HP Hij Hblock).
Qed.

Theorem unbounded_small_backward_pair_implies_eventual_periodicity :
  forall R T P i j,
    (forall N,
      exists extra,
        (N <= extra)%nat /\
        small_backward_pair_block R T P extra (i, j)) ->
    forall t,
      center_window (S R)
        (T + (S i) * P + t + (j - i) * P)%nat =
      center_window (S R)
        (T + (S i) * P + t)%nat.
Proof.
  intros R T P i j Hfar t.
  destruct (Hfar t) as [extra [Hte Hblock]].
  unfold small_backward_pair_block in Hblock.
  simpl in Hblock.
  destruct Hblock as [Hij [_ Hblock]].
  specialize (Hblock t Hte).
  replace (T + (S i) * P + t + (j - i) * P)%nat
    with (T + (S j) * P + t)%nat by lia.
  symmetry.
  exact Hblock.
Qed.

Theorem periodic_tail_at_successor_cutoff_transports_to_bounded_eventual_periodicity :
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
        center_window (S R) (T' + t)%nat.
Proof.
  intros R T P HP Hperiod.
  destruct
    (periodic_tail_at_successor_cutoff_has_unbounded_small_backward_pair
      R T P HP Hperiod)
    as [i [j [Hij Hfar]]].
  pose proof (small_backward_pair_pool_sound i j Hij) as [Hij_lt Hj_le].
  exists (T + (S i) * P)%nat, ((j - i) * P)%nat.
  split.
  - lia.
  - split.
    + assert (Hi4 : (S i <= 4)%nat) by lia.
      apply Nat.add_le_mono_l.
      apply Nat.mul_le_mono_nonneg_r.
      * lia.
      * exact Hi4.
    + split.
      * split.
        -- apply Nat.mul_pos_pos; lia.
        -- assert (Hij4 : (j - i <= 4)%nat) by lia.
           apply Nat.mul_le_mono_nonneg_r.
           ++ lia.
           ++ exact Hij4.
      * exact
          (unbounded_small_backward_pair_implies_eventual_periodicity
            R T P i j Hfar).
Qed.

Theorem uniformly_eventually_periodic_from_transports_to_larger_radius :
  forall R T P,
    uniformly_eventually_periodic_from R (S T) P ->
    exists T' P',
      (T + P <= T')%nat /\
      (T' <= T + 4 * P)%nat /\
      (0 < P' <= 4 * P)%nat /\
      uniformly_eventually_periodic_from (S R) T' P'.
Proof.
  intros R T P [HP Hperiod].
  set (pool := bounded_transport_pair_pool T P).
  assert (Hall :
      forall N,
        exists tp,
          In tp pool /\
          exists extra,
            (N <= extra)%nat /\
            let (T', P') := tp in
            forall t,
              center_window (S R + extra) (T' + t + P')%nat =
              center_window (S R + extra) (T' + t)%nat).
  { intro N.
    destruct
      (periodic_tail_at_successor_cutoff_transports_to_bounded_eventual_periodicity
        (R + N)%nat T P HP
        (proj2
          (uniformly_eventually_periodic_from_shift_radius
            R (S T) P N (conj HP Hperiod))))
      as [T' [P' [Hlow [Hhigh [HP'_bounds Htail]]]]].
    exists (T', P').
    split.
    - unfold pool.
      apply bounded_transport_pair_pool_complete; assumption.
    - exists N.
      split.
      + lia.
      + simpl.
        replace (S R + N)%nat with (S (R + N)) by lia.
        exact Htail.
  }
  destruct
    (finite_list_has_arbitrarily_often_member
      (nat * nat) pool
      (fun tp extra =>
         let (T', P') := tp in
         forall t,
           center_window (S R + extra) (T' + t + P')%nat =
           center_window (S R + extra) (T' + t)%nat)
      Hall)
    as [[T' P'] [Hin Hfar]].
  pose proof (bounded_transport_pair_pool_sound T P T' P' Hin)
    as [Hlow [Hhigh HP'_bounds]].
  exists T', P'.
  split.
  - exact Hlow.
  - split.
    + exact Hhigh.
    + split.
      * exact HP'_bounds.
      * split.
        -- exact (proj1 HP'_bounds).
        -- intros extra t.
           destruct (Hfar extra) as [extra' [Hextra Htail]].
           eapply
             (center_window_eq_weaken
                (S R + extra')%nat
                (S R + extra)%nat
                (T' + t + P')%nat
                (T' + t)%nat).
           ++ lia.
           ++ exact (Htail t).
Qed.

Theorem positive_uniformly_eventually_periodic_from_transports_to_larger_radius :
  forall R T P,
    (0 < T)%nat ->
    uniformly_eventually_periodic_from R T P ->
    exists T' P',
      (0 < T')%nat /\
      uniformly_eventually_periodic_from (S R) T' P'.
Proof.
  intros R T P HT Hunif.
  destruct Hunif as [HP Hperiod].
  destruct T as [|T0].
  - lia.
  - destruct
      (uniformly_eventually_periodic_from_transports_to_larger_radius
        R T0 P (conj HP Hperiod))
      as [T' [P' [Hlow [_ [_ Hlarger]]]]].
    exists T', P'.
    split.
    + lia.
    + exact Hlarger.
Qed.

Theorem positive_uniformly_eventually_periodic_from_iterates :
  forall steps R T P,
    (0 < T)%nat ->
    uniformly_eventually_periodic_from R T P ->
    exists T' P',
      (0 < T')%nat /\
      uniformly_eventually_periodic_from (R + steps) T' P'.
Proof.
  induction steps as [|steps IH]; intros R T P HT Hunif.
  - exists T, P.
    split.
    + exact HT.
    + replace (R + 0)%nat with R by lia.
      exact Hunif.
  - destruct (IH R T P HT Hunif) as [T1 [P1 [HT1 Hunif1]]].
    destruct
      (positive_uniformly_eventually_periodic_from_transports_to_larger_radius
        (R + steps)%nat T1 P1 HT1 Hunif1)
      as [T' [P' [HT' Hunif']]].
    exists T', P'.
    split.
    + exact HT'.
    + replace (R + S steps)%nat with (S (R + steps)) by lia.
      exact Hunif'.
Qed.

Lemma abs_coord_lies_in_centered_interval :
  forall R x,
    in_interval 0%Z (R + Z.to_nat (Z.abs x)) x.
Proof.
  intros R x.
  unfold in_interval.
  destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
    rewrite Habs; simpl; lia.
Qed.

Theorem uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity :
  forall R T P,
    uniformly_eventually_periodic_from R T P ->
    eventually_periodic_full_rows_from T P.
Proof.
  intros R T P [HP Hperiod].
  split.
  - exact HP.
  - intros t x.
    set (extra := Z.to_nat (Z.abs x)).
    pose proof (Hperiod extra t) as Hwindow.
    rewrite <- (row_window_canonical_row (R + extra) (T + t + P)%nat) in Hwindow.
    rewrite <- (row_window_canonical_row (R + extra) (T + t)%nat) in Hwindow.
    apply row_window_eq_implies_same_on_interval in Hwindow.
    apply Hwindow.
    unfold extra.
    apply abs_coord_lies_in_centered_interval.
Qed.

Theorem eventually_periodic_full_rows_from_impossible :
  forall T P,
    eventually_periodic_full_rows_from T P ->
    False.
Proof.
  intros T P [HP Hperiod].
  destruct (canonical_row_no_repetition_pointwise T P HP) as [x Hneq].
  specialize (Hperiod 0%nat x).
  replace (T + 0 + P)%nat with (T + P)%nat in Hperiod by lia.
  replace (T + 0)%nat with T in Hperiod by lia.
  exact (Hneq Hperiod).
Qed.

Theorem uniformly_eventually_periodic_from_impossible :
  forall R T P,
    uniformly_eventually_periodic_from R T P ->
    False.
Proof.
  intros R T P Hunif.
  apply eventually_periodic_full_rows_from_impossible with (T := T) (P := P).
  exact
    (uniformly_eventually_periodic_from_implies_full_row_eventual_periodicity
      R T P Hunif).
Qed.

Theorem realizable_uniform_periodic_tail_from_impossible :
  forall R,
    ~ realizable_uniform_periodic_tail_from R.
Proof.
  intros R [T [P Hunif]].
  exact (uniformly_eventually_periodic_from_impossible R T P Hunif).
Qed.

Theorem realizable_uniform_periodic_tail_impossible :
  ~ exists R T P, uniformly_eventually_periodic_from R T P.
Proof.
  intros [R [T [P Hunif]]].
  exact (uniformly_eventually_periodic_from_impossible R T P Hunif).
Qed.

Theorem faithful_observational_periodic_tail_realizer_impossible :
  forall R,
    faithful_observational_periodic_tail_realizer R -> False.
Proof.
  intros R F.
  exact
    (uniformly_eventually_periodic_from_impossible
      R (foptr_start R F) (foptr_period R F) (foptr_uniform R F)).
Qed.

Theorem realizable_observational_periodic_tail_from_impossible :
  forall R,
    ~ realizable_observational_periodic_tail_from R.
Proof.
  intros R [F].
  exact (faithful_observational_periodic_tail_realizer_impossible R F).
Qed.

Theorem faithful_window_growth_iterates :
  faithful_window_growth_principle ->
  forall steps R T P,
    observational_periodic_tail_from R T P ->
    observational_periodic_tail_from (R + steps) T P.
Proof.
  intros Hgrow steps.
  induction steps as [|steps IH]; intros R T P Hobs.
  - replace (R + 0)%nat with R by lia.
    exact Hobs.
  - replace (R + S steps)%nat with (S (R + steps)) by lia.
    apply Hgrow.
    apply IH.
    exact Hobs.
Qed.

Theorem faithful_window_growth_implies_bhk_window_upgrade :
  faithful_window_growth_principle ->
  bhk_window_upgrade_principle.
Proof.
  intros Hgrow R T P Hobs.
  destruct Hobs as [HP Hperiod].
  split.
  - exact HP.
  - intros extra t.
    destruct
      (faithful_window_growth_iterates
        Hgrow extra R T P (conj HP Hperiod))
      as [_ Hperiod_extra].
    exact (Hperiod_extra t).
Qed.

Theorem observational_periodic_tail_from_impossible_under_bhk_upgrade :
  bhk_window_upgrade_principle ->
  forall R T P,
    observational_periodic_tail_from R T P ->
    False.
Proof.
  intros Hupgrade R T P Hobs.
  apply (uniformly_eventually_periodic_from_impossible R T P).
  exact (Hupgrade R T P Hobs).
Qed.

Theorem eventually_periodic_center_window_impossible_under_bhk_upgrade :
  bhk_window_upgrade_principle ->
  forall R,
    ~ eventually_periodic_center_window R.
Proof.
  intros Hupgrade R [T [P Hobs]].
  eapply observational_periodic_tail_from_impossible_under_bhk_upgrade.
  - exact Hupgrade.
  - exact Hobs.
Qed.

End Mixed_Periodicity.
