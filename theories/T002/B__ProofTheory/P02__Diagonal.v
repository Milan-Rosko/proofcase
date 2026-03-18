(* P02__Diagonal.v *)

From T002 Require Import P00__Concrete_Provability.
From T002 Require Import R01__Foundation_Fibonacci R02__Foundation_Zeckendorf.
From T002 Require Import R04__Verification_Hilbert_Syntax R06__Encoding_Formula_Coding.

Section CodeDiagonal.

Variable hole_code : nat.

Hypothesis unpair_pair_P0 :
  forall a b, unpair P0 (pair P0 a b) = (a, b).

Hypothesis hole_code_not_bot :
  hole_code <> 0.

Hypothesis hole_code_fresh :
  forall a b, hole_code <> S (pair P0 a b).

Definition apply_oform (A : OForm) (t : nat) : nat :=
  subst_code_fuel hole_code (osize A) (enc_oform hole_code A) t.

Fixpoint hole_free (A : OForm) : Prop :=
  match A with
  | O_Bot => True
  | O_Imp a b => hole_free a /\ hole_free b
  | O_Hole => False
  end.

Record Template : Type := {
  template_body : OForm
}.

Definition TemplateAdmissible (T : Template) : Prop :=
  hole_free (template_body T).

Definition apply_template (T : Template) (t : nat) : nat :=
  apply_oform (template_body T) t.

Definition diagonal_seed (T : Template) : nat :=
  apply_template T 0.

Definition UnfoldLaw (T : Template) (g : nat) : Prop :=
  g = apply_template T g.

Definition TemplateOK (T : Template) : Prop :=
  forall t1 t2, apply_template T t1 = apply_template T t2.

Definition UnfoldsAsClosedSubst (T : Template) (g : nat) : Prop :=
  exists theta : Form,
    enc_form theta = g /\
    g = enc_form (close_oform (template_body T) theta).

Theorem apply_oform_closed :
  forall A t,
    ClosedCode t ->
    ClosedCode (apply_oform A t).
Proof.
  intros A t Ht.
  unfold apply_oform.
  apply (subst_code_preserves_closed
           hole_code
           unpair_pair_P0
           hole_code_not_bot
           hole_code_fresh
           A
           t).
  exact Ht.
Qed.

Theorem apply_oform_unfold :
  forall A t,
    apply_oform A t = subst_oform A t.
Proof.
  intros A t.
  unfold apply_oform.
  apply (subst_code_correct
           hole_code
           unpair_pair_P0
           hole_code_not_bot
           hole_code_fresh
           A
           t).
Qed.

Theorem apply_template_closed :
  forall T t,
    ClosedCode t ->
    ClosedCode (apply_template T t).
Proof.
  intros T t Ht.
  unfold apply_template.
  apply apply_oform_closed.
  exact Ht.
Qed.

Theorem apply_template_unfold :
  forall T t,
    apply_template T t = subst_oform (template_body T) t.
Proof.
  intros T t.
  unfold apply_template.
  apply apply_oform_unfold.
Qed.

Theorem apply_template_as_closed_subst :
  forall T t,
    ClosedCode t ->
    exists theta : Form,
      enc_form theta = t /\
      apply_template T t = enc_form (close_oform (template_body T) theta).
Proof.
  intros T t Hclosed.
  destruct Hclosed as [theta Htheta].
  exists theta.
  split.
  - exact Htheta.
  - rewrite apply_template_unfold.
    rewrite close_oform_enc.
    now rewrite Htheta.
Qed.

Theorem diagonal_seed_closed :
  forall T,
    ClosedCode (diagonal_seed T).
Proof.
  intro T.
  unfold diagonal_seed.
  apply apply_template_closed.
  exists F_Bot.
  reflexivity.
Qed.

Theorem diagonal_seed_unfold_closed_subst :
  forall T,
    TemplateOK T ->
    UnfoldsAsClosedSubst T (diagonal_seed T).
Proof.
  intros T Hok.
  unfold UnfoldsAsClosedSubst.
  destruct (apply_template_as_closed_subst T (diagonal_seed T) (diagonal_seed_closed T))
    as [theta [Htheta Happ]].
  exists theta.
  split.
  - exact Htheta.
  - unfold diagonal_seed in *.
    eapply eq_trans.
    + apply Hok.
    + exact Happ.
Qed.

Lemma subst_oform_hole_free :
  forall A t1 t2,
    hole_free A ->
    subst_oform A t1 = subst_oform A t2.
Proof.
  induction A as [|a IHa b IHb|]; intros t1 t2 Hfree; simpl in *.
  - reflexivity.
  - destruct Hfree as [Ha Hb].
    rewrite (IHa t1 t2 Ha), (IHb t1 t2 Hb).
    reflexivity.
  - contradiction.
Qed.

Lemma apply_oform_irrelevant_hole_free :
  forall A t1 t2,
    hole_free A ->
    apply_oform A t1 = apply_oform A t2.
Proof.
  intros A t1 t2 Hfree.
  rewrite !apply_oform_unfold.
  apply subst_oform_hole_free.
  exact Hfree.
Qed.

Lemma template_ok_from_hole_free :
  forall T,
    hole_free (template_body T) ->
    TemplateOK T.
Proof.
  intros T Hfree t1 t2.
  unfold apply_template.
  apply apply_oform_irrelevant_hole_free.
  exact Hfree.
Qed.

Lemma template_ok_from_admissible :
  forall T,
    TemplateAdmissible T ->
    TemplateOK T.
Proof.
  intros T Hadm.
  unfold TemplateAdmissible in Hadm.
  apply template_ok_from_hole_free.
  exact Hadm.
Qed.

Theorem fixed_point_code :
  forall T,
    TemplateOK T ->
    ClosedCode (diagonal_seed T) /\
    UnfoldLaw T (diagonal_seed T).
Proof.
  intros T Hok.
  split.
  - apply diagonal_seed_closed.
  - unfold UnfoldLaw, diagonal_seed.
    apply Hok.
Qed.

Theorem fixed_point_code_unfold :
  forall T,
    TemplateOK T ->
    ClosedCode (diagonal_seed T) /\
    UnfoldLaw T (diagonal_seed T) /\
    UnfoldsAsClosedSubst T (diagonal_seed T).
Proof.
  intros T Hok.
  split.
  - apply diagonal_seed_closed.
  - split.
    + unfold UnfoldLaw, diagonal_seed.
      apply Hok.
    + apply diagonal_seed_unfold_closed_subst.
      exact Hok.
Qed.

Theorem fixed_point_code_hole_free :
  forall A,
    hole_free A ->
    exists g,
      ClosedCode g /\
      g = apply_oform A g.
Proof.
  intros A Hfree.
  set (T := {| template_body := A |}).
  exists (diagonal_seed T).
  destruct (fixed_point_code T (template_ok_from_hole_free T Hfree)) as [Hclosed Hunfold].
  split.
  - exact Hclosed.
  - exact Hunfold.
Qed.

Theorem FixedPoint :
  forall T,
    TemplateAdmissible T ->
    exists g,
      ClosedCode g /\
      UnfoldLaw T g /\
      UnfoldsAsClosedSubst T g.
Proof.
  intros T Hadm.
  exists (diagonal_seed T).
  destruct (fixed_point_code_unfold T (template_ok_from_admissible T Hadm))
    as [Hclosed [Hunfold Hsubst]].
  repeat split; assumption.
Qed.

End CodeDiagonal.