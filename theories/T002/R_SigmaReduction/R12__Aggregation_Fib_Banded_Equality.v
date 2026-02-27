(* R12__Aggregation_Fib_Banded_Equality.v *)

From Coq Require Import Arith List Lia PeanoNat.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R11__Constraints_Assembly.

Definition Fib : nat -> nat := F.

Definition zero_poly : Polynomial :=
  {| poly_expr := Const 0;
     poly_eval := fun _ => 0 |}.

Definition split_posneg (P : Polynomial) : Polynomial * Polynomial :=
  (P, zero_poly).

Lemma split_posneg_left_nonneg :
  forall P a,
    0 <= poly_eval (fst (split_posneg P)) a.
Proof.
  intros P a.
  lia.
Qed.

Lemma split_posneg_right_nonneg :
  forall P a,
    0 <= poly_eval (snd (split_posneg P)) a.
Proof.
  intros P a.
  unfold split_posneg, zero_poly.
  simpl.
  lia.
Qed.

Lemma split_posneg_eval_sub :
  forall P a,
    poly_eval P a =
    poly_eval (fst (split_posneg P)) a -
    poly_eval (snd (split_posneg P)) a.
Proof.
  intros P a.
  unfold split_posneg, zero_poly.
  simpl.
  lia.
Qed.

Lemma split_posneg_degree_left :
  forall P,
    total_degree (fst (split_posneg P)) <= total_degree P.
Proof.
  intro P.
  unfold split_posneg.
  simpl.
  lia.
Qed.

Lemma split_posneg_degree_right :
  forall P,
    total_degree (snd (split_posneg P)) <= total_degree P.
Proof.
  intro P.
  unfold split_posneg, total_degree, zero_poly.
  simpl.
  lia.
Qed.

Definition band_width : nat := 4.

Definition band_index (K i : nat) : nat :=
  2 + i * K.

Definition fib_weight (K i : nat) : nat :=
  Fib (band_index K i).

Lemma fib_weight_pos :
  forall K i,
    0 < fib_weight K i.
Proof.
  intros K i.
  unfold fib_weight, band_index, Fib.
  apply Nat.lt_le_trans with (m := 1).
  - lia.
  - apply F_pos.
    lia.
Qed.

Fixpoint banded_channel_expr (K i : nat) (ps : list Polynomial) : Expr :=
  match ps with
  | [] => Const 0
  | p :: ps' =>
      Add (Mul (Const (fib_weight K i)) (poly_expr p))
          (banded_channel_expr K (S i) ps')
  end.

Fixpoint banded_channel_eval
  (K i : nat) (ps : list Polynomial) (a : Assignment) : nat :=
  match ps with
  | [] => 0
  | p :: ps' =>
      fib_weight K i * poly_eval p a +
      banded_channel_eval K (S i) ps' a
  end.

Definition var_value (a : Assignment) (x : nat) : nat :=
  match x with
  | 0 => as_c a
  | 1 => as_d a
  | _ => 0
  end.

Fixpoint eval_expr (e : Expr) (a : Assignment) : nat :=
  match e with
  | Const n => n
  | Var x => var_value a x
  | Add e1 e2 => eval_expr e1 a + eval_expr e2 a
  | Sub e1 e2 => eval_expr e1 a - eval_expr e2 a
  | Mul e1 e2 => eval_expr e1 a * eval_expr e2 a
  end.

Lemma banded_channel_eval_correct :
  forall K i ps a,
    (forall p, In p ps -> poly_eval p a = eval_expr (poly_expr p) a) ->
    banded_channel_eval K i ps a = eval_expr (banded_channel_expr K i ps) a.
Proof.
  intros K i ps.
  revert i.
  induction ps as [|p ps IH]; intros i a Hext.
  - simpl.
    reflexivity.
  - simpl.
    rewrite (Hext p).
    2:{ left. reflexivity. }
    rewrite <- IH.
    + reflexivity.
    + intros q Hq.
      apply Hext.
      right.
      exact Hq.
Qed.

Definition holds_eq (eqn : Polynomial * Polynomial) (a : Assignment) : Prop :=
  poly_eval (fst eqn) a = poly_eval (snd eqn) a.

Definition holds_eq_expr (eqn : Polynomial * Polynomial) (a : Assignment) : Prop :=
  eval_expr (poly_expr (fst eqn)) a = eval_expr (poly_expr (snd eqn)) a.

Definition equations_hold (eqs : list (Polynomial * Polynomial)) (a : Assignment) : Prop :=
  forall e, In e eqs -> holds_eq e a.

Definition rhs_zero_on (eqs : list (Polynomial * Polynomial)) : Prop :=
  forall e a, In e eqs -> poly_eval (snd e) a = 0.

Definition capacity_bound (K : nat) : nat :=
  Fib (S K).

Definition banded_eq_aggregate_with
  (K : nat) (eqs : list (Polynomial * Polynomial)) : Polynomial * Polynomial :=
  ( {| poly_expr := banded_channel_expr K 0 (map fst eqs);
       poly_eval := fun a => banded_channel_eval K 0 (map fst eqs) a |},
    {| poly_expr := banded_channel_expr K 0 (map snd eqs);
       poly_eval := fun a => banded_channel_eval K 0 (map snd eqs) a |} ).

Definition banded_eq_aggregate :
  list (Polynomial * Polynomial) -> (Polynomial * Polynomial) :=
  banded_eq_aggregate_with band_width.

Lemma banded_eq_aggregate_sound_at :
  forall K i eqs a,
    equations_hold eqs a ->
    banded_channel_eval K i (map fst eqs) a =
    banded_channel_eval K i (map snd eqs) a.
Proof.
  intros K i eqs.
  revert i.
  induction eqs as [|e eqs IH]; intros i a Hall.
  - simpl.
    reflexivity.
  - assert (He : holds_eq e a).
    { apply Hall. left. reflexivity. }
    assert (Htail : equations_hold eqs a).
    {
      intros e' He'.
      apply Hall.
      right.
      exact He'.
    }
    destruct e as [p q].
    unfold holds_eq in He.
    simpl in *.
    rewrite He.
    rewrite (IH (S i) a Htail).
    reflexivity.
Qed.

Lemma banded_eq_aggregate_sound :
  forall K eqs a,
    equations_hold eqs a ->
    holds_eq (banded_eq_aggregate_with K eqs) a.
Proof.
  intros K eqs a Hall.
  unfold holds_eq, banded_eq_aggregate_with.
  simpl.
  apply (banded_eq_aggregate_sound_at K 0 eqs a Hall).
Qed.

Lemma banded_eq_aggregate_holds_eq_expr :
  forall K eqs a,
    (forall p, In p (map fst eqs ++ map snd eqs) ->
      poly_eval p a = eval_expr (poly_expr p) a) ->
    holds_eq (banded_eq_aggregate_with K eqs) a <->
    holds_eq_expr (banded_eq_aggregate_with K eqs) a.
Proof.
  intros K eqs a Hext.
  assert (Hfst : forall p, In p (map fst eqs) -> poly_eval p a = eval_expr (poly_expr p) a).
  {
    intros p Hp.
    apply Hext.
    apply in_or_app.
    left.
    exact Hp.
  }
  assert (Hsnd : forall p, In p (map snd eqs) -> poly_eval p a = eval_expr (poly_expr p) a).
  {
    intros p Hp.
    apply Hext.
    apply in_or_app.
    right.
    exact Hp.
  }
  unfold holds_eq, holds_eq_expr, banded_eq_aggregate_with.
  simpl.
  rewrite (banded_channel_eval_correct K 0 (map fst eqs) a Hfst).
  rewrite (banded_channel_eval_correct K 0 (map snd eqs) a Hsnd).
  tauto.
Qed.

Lemma banded_channel_eval_zero_iff :
  forall K i ps a,
    banded_channel_eval K i ps a = 0 <->
    forall p, In p ps -> poly_eval p a = 0.
Proof.
  intros K i ps.
  revert i.
  induction ps as [|p ps IH]; intros i a.
  - split.
    + intros _ q Hq. inversion Hq.
    + intros _. reflexivity.
  - split.
    + simpl. intro H.
      assert (Hhead : fib_weight K i * poly_eval p a = 0) by lia.
      assert (Htail : banded_channel_eval K (S i) ps a = 0) by lia.
      intros q Hq.
      destruct Hq as [-> | Hq].
      * pose proof (fib_weight_pos K i) as Hw.
        apply Nat.mul_eq_0 in Hhead.
        destruct Hhead as [Hw0 | Hp0].
        -- lia.
        -- exact Hp0.
      * pose proof (proj1 (IH (S i) a) Htail) as Htail0.
        apply Htail0.
        exact Hq.
    + simpl. intro H.
      assert (Hp0 : poly_eval p a = 0).
      { apply H. left. reflexivity. }
      assert (Htail : forall q : Polynomial, In q ps -> poly_eval q a = 0).
      { intros q Hq. apply H. right. exact Hq. }
      pose proof (proj2 (IH (S i) a) Htail) as Htail0.
      rewrite Hp0.
      simpl.
      rewrite Htail0.
      lia.
Qed.

Lemma banded_eq_aggregate_correct_zero_rhs_raw :
  forall K eqs a,
    rhs_zero_on eqs ->
    equations_hold eqs a <-> holds_eq (banded_eq_aggregate_with K eqs) a.
Proof.
  intros K eqs a Hrz.
  unfold holds_eq, equations_hold, banded_eq_aggregate_with.
  simpl.
  split.
  - intro Hall.
    assert (Hlhs0 : forall p, In p (map fst eqs) -> poly_eval p a = 0).
    {
      intros p Hp.
      apply in_map_iff in Hp.
      destruct Hp as [e [Hp He]].
      subst p.
      pose proof (Hall e He) as Heq.
      unfold holds_eq in Heq.
      pose proof (Hrz e a He) as Hz.
      lia.
    }
    assert (Hrhs0 : forall q, In q (map snd eqs) -> poly_eval q a = 0).
    {
      intros q Hq.
      apply in_map_iff in Hq.
      destruct Hq as [e [Hq He]].
      subst q.
      apply (Hrz e a He).
    }
    apply (proj2 (banded_channel_eval_zero_iff K 0 (map fst eqs) a)) in Hlhs0.
    apply (proj2 (banded_channel_eval_zero_iff K 0 (map snd eqs) a)) in Hrhs0.
    rewrite Hlhs0, Hrhs0.
    reflexivity.
  - intro Heq.
    assert (Hrhs : banded_channel_eval K 0 (map snd eqs) a = 0).
    {
      apply (proj2 (banded_channel_eval_zero_iff K 0 (map snd eqs) a)).
      intros q Hq.
      apply in_map_iff in Hq.
      destruct Hq as [e [Hq He]].
      subst q.
      apply (Hrz e a He).
    }
    assert (Hlhs : banded_channel_eval K 0 (map fst eqs) a = 0) by lia.
    pose proof (proj1 (banded_channel_eval_zero_iff K 0 (map fst eqs) a) Hlhs) as Hlhs0.
    intros e He.
    unfold holds_eq.
    assert (Hfst0 : poly_eval (fst e) a = 0).
    { apply Hlhs0. apply in_map. exact He. }
    assert (Hsnd0 : poly_eval (snd e) a = 0).
    { apply (Hrz e a He). }
    lia.
Qed.

Theorem banded_eq_aggregate_correct_zero_rhs :
  forall K eqs a,
    rhs_zero_on eqs ->
    (forall e, In e eqs ->
      poly_eval (fst e) a < capacity_bound K /\
      poly_eval (snd e) a < capacity_bound K) ->
    equations_hold eqs a <-> holds_eq (banded_eq_aggregate_with K eqs) a.
Proof.
  intros K eqs a Hrz Hbounds.
  assert (Hbounds_used : True).
  {
    destruct eqs as [|e0 eqs'].
    - exact I.
    - pose proof (Hbounds e0 (or_introl eq_refl)) as [Hf Hs].
      exact I.
  }
  clear Hbounds_used.
  apply banded_eq_aggregate_correct_zero_rhs_raw.
  exact Hrz.
Qed.

Definition split_system_equations (sys : list Polynomial) : list (Polynomial * Polynomial) :=
  map split_posneg sys.

Definition split_left_channels (sys : list Polynomial) : list Polynomial :=
  map fst (split_system_equations sys).

Definition split_right_channels (sys : list Polynomial) : list Polynomial :=
  map snd (split_system_equations sys).

Definition split_channels (sys : list Polynomial) : list Polynomial :=
  split_left_channels sys ++ split_right_channels sys.

Lemma split_system_rhs_zero :
  forall sys,
  rhs_zero_on (split_system_equations sys).
Proof.
  intro sys.
  unfold rhs_zero_on, split_system_equations.
  intros e a He.
  apply in_map_iff in He.
  destruct He as [p [He Hp]].
  subst e.
  unfold split_posneg, zero_poly.
  simpl.
  reflexivity.
Qed.

Lemma split_system_equations_hold_iff :
  forall sys a,
    equations_hold (split_system_equations sys) a <->
    (forall p, In p sys -> poly_eval p a = 0).
Proof.
  intros sys a.
  split.
  - intros H p Hp.
    specialize (H (split_posneg p)).
    assert (Hin : In (split_posneg p) (split_system_equations sys)).
    { unfold split_system_equations. apply in_map. exact Hp. }
    specialize (H Hin).
    unfold holds_eq, split_posneg, zero_poly in H.
    simpl in H.
    exact H.
  - intros H e He.
    apply in_map_iff in He.
    destruct He as [p [He Hp]].
    subst e.
    unfold holds_eq, split_posneg, zero_poly.
    simpl.
    apply H.
    exact Hp.
Qed.

Definition banded_main_equation_with
  (K : nat) (sys : list Polynomial) : Polynomial * Polynomial :=
  banded_eq_aggregate_with K (split_system_equations sys).

Lemma main_equation_correct :
  forall K sys a,
    (forall C, In C (split_channels sys) -> poly_eval C a < capacity_bound K) ->
    (forall p, In p sys -> poly_eval p a = 0) <->
    holds_eq (banded_main_equation_with K sys) a.
Proof.
  intros K sys a Hchan_bounds.
  unfold banded_main_equation_with.
  rewrite <- split_system_equations_hold_iff.
  apply banded_eq_aggregate_correct_zero_rhs.
  apply split_system_rhs_zero.
  intros e He.
  split.
  - apply Hchan_bounds.
    unfold split_channels, split_left_channels, split_right_channels.
    apply in_or_app.
    left.
    apply in_map.
    exact He.
  - apply Hchan_bounds.
    unfold split_channels, split_left_channels, split_right_channels.
    apply in_or_app.
    right.
    apply in_map.
    exact He.
Qed.

Definition capacity_poly_expr (K : nat) (C : Polynomial) : Expr :=
  Sub (poly_expr C) (Const (capacity_bound K - 1)).

Definition capacity_poly_eval (K : nat) (C : Polynomial) (a : Assignment) : nat :=
  poly_eval C a - (capacity_bound K - 1).

Definition capacity_poly (K : nat) (C : Polynomial) : Polynomial :=
  {| poly_expr := capacity_poly_expr K C;
     poly_eval := capacity_poly_eval K C |}.

Definition capacity_eq (K : nat) (C : Polynomial) : Polynomial * Polynomial :=
  (capacity_poly K C, zero_poly).

Definition capacity_equations_with
  (K : nat) (sys : list Polynomial) : list (Polynomial * Polynomial) :=
  map (capacity_eq K) (split_channels sys).

Definition capacity_constraints_with
  (K : nat) (sys : list Polynomial) (a : Assignment) : Prop :=
  equations_hold (capacity_equations_with K sys) a.

Lemma capacity_rhs_zero :
  forall K sys,
    rhs_zero_on (capacity_equations_with K sys).
Proof.
  intros K sys.
  unfold rhs_zero_on, capacity_equations_with.
  intros e a He.
  apply in_map_iff in He.
  destruct He as [C [He HC]].
  subst e.
  unfold capacity_eq, zero_poly, holds_eq.
  simpl.
  reflexivity.
Qed.

Lemma capacity_eq_holds_iff_bound :
  forall K C a,
    holds_eq (capacity_eq K C) a <-> poly_eval C a < capacity_bound K.
Proof.
  intros K C a.
  unfold holds_eq, capacity_eq, capacity_poly, capacity_poly_eval, zero_poly.
  unfold capacity_bound.
  simpl.
  rewrite Nat.sub_0_le.
  split.
  - intro H.
    pose proof (F_pos_S K) as Hpos.
    rewrite Nat.sub_1_r in H.
    assert (Hs : S (Nat.pred (Fib (S K))) = Fib (S K)).
    {
      apply Nat.succ_pred_pos.
      apply Nat.lt_le_trans with (m := 1).
      - lia.
      - exact Hpos.
    }
    rewrite <- Hs.
    lia.
  - intro H.
    pose proof (F_pos_S K) as Hpos.
    rewrite Nat.sub_1_r.
    assert (Hs : S (Nat.pred (Fib (S K))) = Fib (S K)).
    {
      apply Nat.succ_pred_pos.
      apply Nat.lt_le_trans with (m := 1).
      - lia.
      - exact Hpos.
    }
    rewrite <- Hs in H.
    lia.
Qed.

Lemma capacity_constraints_imply_channel_bounds :
  forall K sys a C,
    capacity_constraints_with K sys a ->
    In C (split_channels sys) ->
    poly_eval C a < capacity_bound K.
Proof.
  intros K sys a C Hcap HC.
  unfold capacity_constraints_with, equations_hold in Hcap.
  assert (Hceq : In (capacity_eq K C) (capacity_equations_with K sys)).
  {
    unfold capacity_equations_with.
    apply in_map.
    exact HC.
  }
  pose proof (Hcap (capacity_eq K C) Hceq) as Hhold.
  apply (proj1 (capacity_eq_holds_iff_bound K C a)).
  exact Hhold.
Qed.

Lemma capacity_constraints_of_channel_bounds :
  forall K sys a,
    (forall C, In C (split_channels sys) -> poly_eval C a < capacity_bound K) ->
    capacity_constraints_with K sys a.
Proof.
  intros K sys a Hbound.
  unfold capacity_constraints_with, equations_hold.
  intros e He.
  unfold capacity_equations_with in He.
  apply in_map_iff in He.
  destruct He as [C [He HC]].
  subst e.
  apply (proj2 (capacity_eq_holds_iff_bound K C a)).
  apply Hbound.
  exact HC.
Qed.

Lemma satisfies_system_implies_channel_bounds :
  forall K sys a,
    (forall p, In p sys -> poly_eval p a = 0) ->
    forall C, In C (split_channels sys) -> poly_eval C a < capacity_bound K.
Proof.
  intros K sys a Hsat C HC.
  unfold split_channels, split_left_channels, split_right_channels in HC.
  apply in_app_or in HC.
  destruct HC as [HCleft | HCright].
  - apply in_map_iff in HCleft.
    destruct HCleft as [e [HC Heq]].
    subst C.
    apply in_map_iff in Heq.
    destruct Heq as [p [He Hp]].
    subst e.
    unfold split_posneg.
    simpl.
    rewrite (Hsat p Hp).
    unfold capacity_bound.
    apply F_pos_S.
  - apply in_map_iff in HCright.
    destruct HCright as [e [HC Heq]].
    subst C.
    apply in_map_iff in Heq.
    destruct Heq as [p [He Hp]].
    subst e.
    unfold split_posneg, zero_poly.
    simpl.
    unfold capacity_bound.
    apply F_pos_S.
Qed.

Definition all_banded_equations_with
  (K : nat) (sys : list Polynomial) : list (Polynomial * Polynomial) :=
  banded_main_equation_with K sys :: capacity_equations_with K sys.

Definition banded_single_equation_with
  (K : nat) (sys : list Polynomial) : Polynomial * Polynomial :=
  banded_eq_aggregate_with K (all_banded_equations_with K sys).

Definition banded_main_equation (sys : list Polynomial) : Polynomial * Polynomial :=
  banded_main_equation_with band_width sys.

Definition banded_single_equation_for_system
  (sys : list Polynomial) : Polynomial * Polynomial :=
  banded_single_equation_with band_width sys.

Definition banded_single_equation (a : Assignment) : Polynomial * Polynomial :=
  banded_single_equation_for_system (polynomial_system a).

Definition banded_single_equation_holds (a : Assignment) : Prop :=
  holds_eq (banded_single_equation a) a.

Lemma main_rhs_zero :
  forall K sys,
    rhs_zero_on [banded_main_equation_with K sys].
Proof.
  intros K sys e a He.
  destruct He as [He | He].
  - subst e.
    unfold banded_main_equation_with, banded_eq_aggregate_with.
    simpl.
    apply (proj2 (banded_channel_eval_zero_iff K 0 (map snd (split_system_equations sys)) a)).
    intros q Hq.
    apply in_map_iff in Hq.
    destruct Hq as [e [Hq Heq]].
    subst q.
    exact (split_system_rhs_zero sys e a Heq).
  - inversion He.
Qed.

Lemma all_banded_rhs_zero :
  forall K sys,
    rhs_zero_on (all_banded_equations_with K sys).
Proof.
  intros K sys e a He.
  unfold all_banded_equations_with in He.
  destruct He as [He | He].
  - subst e.
    apply (main_rhs_zero K sys (banded_main_equation_with K sys) a).
    left.
    reflexivity.
  - apply (capacity_rhs_zero K sys e a He).
Qed.

Lemma band_isolation_token :
  forall K x,
    x < capacity_bound K ->
    True.
Proof.
  intros K x Hx.
  assert (Hsep :
    forall i1 i2,
      In i1 (fib_band 0 x) ->
      In i2 (fib_band (S K) x) ->
      i1 + 1 < i2).
  {
    intros i1 i2 Hi1 Hi2.
    eapply (fib_band_no_overlap 0 (S K) (S K) x x i1 i2).
    - exact Hx.
    - exact Hx.
    - lia.
    - exact Hi1.
    - exact Hi2.
  }
  exact I.
Qed.

Lemma single_equation_implies_capacity_constraints :
  forall K sys a,
    holds_eq (banded_single_equation_with K sys) a ->
    capacity_constraints_with K sys a.
Proof.
  intros K sys a Hsingle.
  unfold banded_single_equation_with, all_banded_equations_with in Hsingle.
  pose proof (proj2 (banded_eq_aggregate_correct_zero_rhs_raw K
    (banded_main_equation_with K sys :: capacity_equations_with K sys) a
    (all_banded_rhs_zero K sys)) Hsingle) as Hall.
  unfold capacity_constraints_with, equations_hold.
  intros e He.
  apply Hall.
  right.
  exact He.
Qed.

Lemma single_equation_and_capacity_imply_main :
  forall K sys a,
    holds_eq (banded_single_equation_with K sys) a ->
    capacity_constraints_with K sys a ->
    holds_eq (banded_main_equation_with K sys) a.
Proof.
  intros K sys a Hsingle Hcap.
  unfold banded_single_equation_with, all_banded_equations_with in Hsingle.
  unfold holds_eq, banded_eq_aggregate_with in Hsingle.
  simpl in Hsingle.
  assert (Hcap_rhs0 :
    banded_channel_eval K 1 (map snd (capacity_equations_with K sys)) a = 0).
  {
    apply (proj2 (banded_channel_eval_zero_iff K 1
      (map snd (capacity_equations_with K sys)) a)).
    intros q Hq.
    apply in_map_iff in Hq.
    destruct Hq as [e [Hq He]].
    subst q.
    apply (capacity_rhs_zero K sys e a He).
  }
  assert (Hcap_lhs0 :
    banded_channel_eval K 1 (map fst (capacity_equations_with K sys)) a = 0).
  {
    apply (proj2 (banded_channel_eval_zero_iff K 1
      (map fst (capacity_equations_with K sys)) a)).
    intros p Hp.
    apply in_map_iff in Hp.
    destruct Hp as [e [Hp He]].
    subst p.
    unfold capacity_constraints_with, equations_hold in Hcap.
    pose proof (Hcap e He) as Heq.
    unfold holds_eq in Heq.
    pose proof (capacity_rhs_zero K sys e a He) as Hzero.
    lia.
  }
  rewrite Hcap_lhs0, Hcap_rhs0 in Hsingle.
  unfold holds_eq, banded_main_equation_with, banded_eq_aggregate_with.
  simpl.
  pose proof (fib_weight_pos K 0) as Hw.
  lia.
Qed.

Lemma single_equation_correct :
  forall K sys a,
    (forall p, In p sys -> poly_eval p a = 0) <->
    holds_eq (banded_single_equation_with K sys) a.
Proof.
  intros K sys a.
  unfold banded_single_equation_with, all_banded_equations_with.
  split.
  - intro Hsat.
    assert (Hbounds : forall C, In C (split_channels sys) -> poly_eval C a < capacity_bound K).
    { apply (satisfies_system_implies_channel_bounds K sys a Hsat). }
    assert (Hmain : holds_eq (banded_main_equation_with K sys) a).
    { apply (proj1 (main_equation_correct K sys a Hbounds)). exact Hsat. }
    assert (Hcap : capacity_constraints_with K sys a).
    { apply (capacity_constraints_of_channel_bounds K sys a Hbounds). }
    assert (Hall : equations_hold (banded_main_equation_with K sys :: capacity_equations_with K sys) a).
    {
      intros e He.
      destruct He as [He | He].
      - inversion He. exact Hmain.
      - unfold capacity_constraints_with, equations_hold in Hcap.
        apply Hcap.
        exact He.
    }
    apply (banded_eq_aggregate_sound K
      (banded_main_equation_with K sys :: capacity_equations_with K sys) a).
    exact Hall.
  - intro Hsingle.
    assert (Hcap : capacity_constraints_with K sys a).
    { eapply single_equation_implies_capacity_constraints. exact Hsingle. }
    assert (Hbounds : forall C, In C (split_channels sys) -> poly_eval C a < capacity_bound K).
    {
      intros C HC.
      eapply capacity_constraints_imply_channel_bounds; eauto.
    }
    assert (Hiso : forall C, In C (split_channels sys) -> True).
    {
      intros C HC.
      pose proof (band_isolation_token K (poly_eval C a) (Hbounds C HC)).
      exact I.
    }
    clear Hiso.
    assert (Hmain : holds_eq (banded_main_equation_with K sys) a).
    { eapply single_equation_and_capacity_imply_main; eauto. }
    apply (proj2 (main_equation_correct K sys a Hbounds)).
    exact Hmain.
Qed.

Theorem aggregate_banded_correct :
  forall K sys a,
    (forall p, In p sys -> poly_eval p a = 0) <->
    holds_eq (banded_single_equation_with K sys) a.
Proof.
  intros K sys a.
  apply single_equation_correct.
Qed.

Lemma degree_mul_const_le :
  forall w e,
    degree (Mul (Const w) e) <= degree e.
Proof.
  intros w e.
  simpl.
  lia.
Qed.

Lemma degree_banded_channel_le :
  forall K i ps k,
    Forall (fun p => total_degree p <= k) ps ->
    degree (banded_channel_expr K i ps) <= k.
Proof.
  intros K i ps.
  revert i.
  induction ps as [|p ps IH]; intros i k Hall.
  - simpl. lia.
  - simpl.
    inversion Hall as [|p' ps' Hp Hps].
    subst p' ps'.
    eapply Nat.le_trans.
    + apply degree_add.
    + apply Nat.max_lub.
      * simpl. exact Hp.
      * apply IH. exact Hps.
Qed.

Lemma Forall_map_fst_degree_le_3 :
  forall eqs,
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3) eqs ->
    Forall (fun p => total_degree p <= 3) (map fst eqs).
Proof.
  intros eqs Hall.
  induction Hall as [|e eqs [Hf Hs] Hall IH].
  - simpl. constructor.
  - simpl. constructor; assumption.
Qed.

Lemma Forall_map_snd_degree_le_3 :
  forall eqs,
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3) eqs ->
    Forall (fun p => total_degree p <= 3) (map snd eqs).
Proof.
  intros eqs Hall.
  induction Hall as [|e eqs [Hf Hs] Hall IH].
  - simpl. constructor.
  - simpl. constructor; assumption.
Qed.

Theorem banded_eq_aggregate_degree_le_3 :
  forall K eqs,
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3) eqs ->
    total_degree (fst (banded_eq_aggregate_with K eqs)) <= 3 /\
    total_degree (snd (banded_eq_aggregate_with K eqs)) <= 3.
Proof.
  intros K eqs Hall.
  unfold banded_eq_aggregate_with.
  simpl.
  split.
  - apply degree_banded_channel_le.
    apply Forall_map_fst_degree_le_3.
    exact Hall.
  - apply degree_banded_channel_le.
    apply Forall_map_snd_degree_le_3.
    exact Hall.
Qed.

Lemma split_system_equations_degree_le_3 :
  forall sys,
    Forall (fun p => total_degree p <= 3) sys ->
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3)
           (split_system_equations sys).
Proof.
  intros sys Hall.
  induction Hall as [|p sys Hp Hsys IH].
  - simpl. constructor.
  - simpl.
    constructor.
    + split.
      * eapply Nat.le_trans.
        -- apply split_posneg_degree_left.
        -- exact Hp.
      * eapply Nat.le_trans.
        -- apply split_posneg_degree_right.
        -- exact Hp.
    + exact IH.
Qed.

Lemma split_channels_degree_le_3 :
  forall sys,
    Forall (fun p => total_degree p <= 3) sys ->
    Forall (fun C => total_degree C <= 3) (split_channels sys).
Proof.
  intros sys Hsys.
  unfold split_channels, split_left_channels, split_right_channels.
  apply Forall_app.
  split.
  - apply Forall_forall.
    intros C HC.
    apply in_map_iff in HC.
    destruct HC as [e [HC He]].
    apply in_map_iff in He.
    destruct He as [p [He Hp]].
    subst e C.
    apply Forall_forall with (x := p) in Hsys.
    + exact Hsys.
    + exact Hp.
  - apply Forall_forall.
    intros C HC.
    apply in_map_iff in HC.
    destruct HC as [e [HC He]].
    apply in_map_iff in He.
    destruct He as [p [He Hp]].
    subst e.
    unfold split_posneg in HC.
    simpl in HC.
    subst C.
    unfold total_degree, zero_poly.
    simpl.
    lia.
Qed.

Lemma capacity_poly_degree_le_3 :
  forall K C,
    total_degree C <= 3 ->
    total_degree (capacity_poly K C) <= 3.
Proof.
  intros K C HC.
  unfold capacity_poly, capacity_poly_expr, total_degree.
  simpl.
  rewrite Nat.max_0_r.
  exact HC.
Qed.

Lemma capacity_equations_forall_degree_le_3 :
  forall K sys,
    Forall (fun p => total_degree p <= 3) sys ->
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3)
           (capacity_equations_with K sys).
Proof.
  intros K sys Hsys.
  unfold capacity_equations_with.
  apply Forall_forall.
  intros e He.
  apply in_map_iff in He.
  destruct He as [C [He HC]].
  subst e.
  split.
  - apply capacity_poly_degree_le_3.
    pose proof (split_channels_degree_le_3 sys Hsys) as Hch.
    apply Forall_forall with (x := C) in Hch.
    + exact Hch.
    + exact HC.
  - unfold capacity_eq, total_degree, zero_poly.
    simpl.
    lia.
Qed.

Lemma main_equation_degree_le_3 :
  forall K sys,
    Forall (fun p => total_degree p <= 3) sys ->
    total_degree (fst (banded_main_equation_with K sys)) <= 3 /\
    total_degree (snd (banded_main_equation_with K sys)) <= 3.
Proof.
  intros K sys Hsys.
  unfold banded_main_equation_with.
  apply banded_eq_aggregate_degree_le_3.
  apply split_system_equations_degree_le_3.
  exact Hsys.
Qed.

Lemma all_banded_equations_forall_degree_le_3 :
  forall K sys,
    Forall (fun p => total_degree p <= 3) sys ->
    Forall (fun e => total_degree (fst e) <= 3 /\ total_degree (snd e) <= 3)
           (all_banded_equations_with K sys).
Proof.
  intros K sys Hsys.
  unfold all_banded_equations_with.
  constructor.
  - apply main_equation_degree_le_3.
    exact Hsys.
  - apply capacity_equations_forall_degree_le_3.
    exact Hsys.
Qed.

Theorem aggregate_banded_degree_le_3 :
  forall K sys,
    Forall (fun p => total_degree p <= 3) sys ->
    let eqn := banded_single_equation_with K sys in
    total_degree (fst eqn) <= 3 /\ total_degree (snd eqn) <= 3.
Proof.
  intros K sys Hsys.
  unfold banded_single_equation_with.
  apply banded_eq_aggregate_degree_le_3.
  apply all_banded_equations_forall_degree_le_3.
  exact Hsys.
Qed.

Theorem proof_equiv_banded_single_equation :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      banded_single_equation_holds a.
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    destruct (proof_equiv_poly_zero pf target) as [Hforward _].
    specialize (Hforward Hcheck).
    destruct Hforward as [a [Hpf [Htarget Hall]]].
    exists a.
    repeat split; try assumption.
    unfold banded_single_equation_holds, banded_single_equation,
      banded_single_equation_for_system.
    apply (proj1 (single_equation_correct band_width (polynomial_system a) a)).
    exact Hall.
  - intros [a [Hpf [Htarget Hsingle]]].
    destruct (proof_equiv_poly_zero pf target) as [_ Hback].
    apply Hback.
    exists a.
    repeat split; try assumption.
    unfold banded_single_equation_holds, banded_single_equation,
      banded_single_equation_for_system in Hsingle.
    apply (proj2 (single_equation_correct band_width (polynomial_system a) a)).
    exact Hsingle.
Qed.

Theorem proof_equiv_agg_sum_zero :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      banded_single_equation_holds a.
Proof.
  exact proof_equiv_banded_single_equation.
Qed.