(* R12__Sum_of_Squares.v *)

From Coq Require Import Arith List Lia.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Import
  R03__Encoding_Beta
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R11__Constraints_Assembly.

Definition agg_sum (sys : list Polynomial) (a : Assignment) : nat :=
  fold_right Nat.add 0 (map (fun p => poly_eval p a) sys).

Definition Agg (a : Assignment) : Expr :=
  fold_right Add (Const 0)
    (map (fun p => Mul (poly_expr p) (poly_expr p)) (polynomial_system a)).

Lemma degree_fold_add_le :
  forall es k,
    Forall (fun e => degree e <= k) es ->
    degree (fold_right Add (Const 0) es) <= k.
Proof.
  induction es as [|e es IH]; intros k Hall.
  - simpl. lia.
  - simpl.
    inversion Hall as [|e' es' He Hes]; subst.
    eapply Nat.le_trans.
    + apply degree_add.
    + apply Nat.max_lub.
      * exact He.
      * apply IH. exact Hes.
Qed.

Lemma degree_square_le_6 :
  forall e,
    degree e <= 3 ->
    degree (Mul e e) <= 6.
Proof.
  intros e He.
  rewrite degree_square.
  lia.
Qed.

Lemma for_all_square_degree_le_6 :
  forall ps,
    Forall (fun p => total_degree p <= 3) ps ->
    Forall (fun e => degree e <= 6)
      (map (fun p => Mul (poly_expr p) (poly_expr p)) ps).
Proof.
  intros ps Hall.
  induction Hall as [|p ps Hp Hps IH].
  - simpl. constructor.
  - simpl.
    constructor.
    + apply degree_square_le_6.
      exact Hp.
    + exact IH.
Qed.

Theorem aggregation_degree :
  forall a,
    degree (Agg a) <= 6.
Proof.
  intro a.
  unfold Agg.
  apply degree_fold_add_le.
  apply for_all_square_degree_le_6.
  apply polynomial_system_forall_degree_le_3.
Qed.

Lemma agg_sum_zero_iff_all_zero :
  forall sys a,
    agg_sum sys a = 0 <-> forall p, In p sys -> poly_eval p a = 0.
Proof.
  induction sys as [|p ps IH]; intros a; split; intro H.
  - intros q Hq. inversion Hq.
  - reflexivity.
  - unfold agg_sum in H. simpl in H.
    intros q Hq.
    assert (Hp : poly_eval p a = 0) by lia.
    assert (Hps_fold : fold_right Nat.add 0 (map (fun q => poly_eval q a) ps) = 0) by lia.
    assert (Hps : agg_sum ps a = 0).
    { unfold agg_sum. exact Hps_fold. }
    destruct Hq as [-> | Hq']; [exact Hp|].
    pose proof (proj1 (IH a) Hps) as Hall.
    exact (Hall q Hq').
  - unfold agg_sum. simpl.
    assert (Hp : poly_eval p a = 0) by (apply H; left; reflexivity).
    assert (Hps : forall q : Polynomial, In q ps -> poly_eval q a = 0).
    { intros q Hq. apply H. right. exact Hq. }
    pose proof (proj2 (IH a) Hps) as Hsum.
    unfold agg_sum in Hsum.
    lia.
Qed.

Theorem proof_equiv_agg_sum_zero :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      as_d a = beta_d (map enc_form pf) /\
      agg_sum (polynomial_system a) a = 0.
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    destruct (proof_equiv_poly_zero pf target) as [Hforward _].
    specialize (Hforward Hcheck).
    destruct Hforward as [a [Hpf [Htarget [Hd Hall]]]].
    exists a.
    repeat split; try assumption.
    apply (proj2 (agg_sum_zero_iff_all_zero (polynomial_system a) a)).
    exact Hall.
  - intros [a [Hpf [Htarget [Hd Hagg]]]].
    destruct (proof_equiv_poly_zero pf target) as [_ Hback].
    apply Hback.
    exists a.
    repeat split; try assumption.
    apply (proj1 (agg_sum_zero_iff_all_zero (polynomial_system a) a)).
    exact Hagg.
Qed.