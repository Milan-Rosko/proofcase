(* R04__Hilbert_Syntax.v *)

From Coq Require Import Init.Logic Arith List Bool.
Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive Form : Type :=
  | F_Bot : Form
  | F_Imp : Form -> Form -> Form.

Definition Imp (A B : Form) : Form := F_Imp A B.
Definition Bot : Form := F_Bot.

Fixpoint form_eqb (A B : Form) : bool :=
  match A, B with
  | F_Bot, F_Bot => true
  | F_Imp A1 A2, F_Imp B1 B2 =>
      andb (form_eqb A1 B1) (form_eqb A2 B2)
  | _, _ => false
  end.

Lemma form_eqb_refl : forall A, form_eqb A A = true.
Proof.
  induction A as [|A1 IH1 A2 IH2].
  - reflexivity.
  - simpl. rewrite IH1. exact IH2.
Qed.

Lemma form_eqb_true_eq : forall A B, form_eqb A B = true -> A = B.
Proof.
  induction A as [|A1 IH1 A2 IH2]; intros B H.
  - destruct B; [reflexivity|discriminate].
  - destruct B; [discriminate|].
    simpl in H.
    apply Bool.andb_true_iff in H as [H1 H2].
    apply IH1 in H1; subst.
    apply IH2 in H2; subst.
    reflexivity.
Qed.

Inductive Ax : Form -> Prop :=
  | Ax_K   : forall A B, Ax (Imp A (Imp B A))
  | Ax_S   : forall A B C,
      Ax (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C)))
  | Ax_EFQ : forall A, Ax (Imp Bot A).

Definition is_K (phi : Form) : bool :=
  match phi with
  | F_Imp A (F_Imp _ A') => form_eqb A A'
  | _ => false
  end.

Definition is_EFQ (phi : Form) : bool :=
  match phi with
  | F_Imp F_Bot _ => true
  | _ => false
  end.

Definition is_S (phi : Form) : bool :=
  match phi with
  | F_Imp (F_Imp A (F_Imp B C))
          (F_Imp (F_Imp A1 B1) (F_Imp A2 C2)) =>
      andb (andb (form_eqb A A1) (form_eqb A A2))
           (andb (form_eqb B B1) (form_eqb C C2))
  | _ => false
  end.

Definition is_axiom (phi : Form) : bool :=
  orb (is_EFQ phi) (orb (is_K phi) (is_S phi)).

Lemma is_K_sound : forall phi, is_K phi = true -> Ax phi.
Proof.
  intros phi H.
  destruct phi as [|A R]; simpl in H; try discriminate.
  destruct R as [|B A']; simpl in H; try discriminate.
  apply form_eqb_true_eq in H; subst.
  apply Ax_K.
Qed.

Lemma is_EFQ_sound : forall phi, is_EFQ phi = true -> Ax phi.
Proof.
  intros phi H.
  destruct phi as [|L R]; simpl in H; try discriminate.
  destruct L; simpl in H; try discriminate.
  apply Ax_EFQ.
Qed.

Lemma is_S_sound : forall phi, is_S phi = true -> Ax phi.
Proof.
  intros phi H.
  destruct phi as [|L R]; simpl in H; try discriminate.
  destruct L as [|A LR]; simpl in H; try discriminate.
  destruct LR as [|B C]; simpl in H; try discriminate.
  destruct R as [|R1 R2]; simpl in H; try discriminate.
  destruct R1 as [|A1 B1]; simpl in H; try discriminate.
  destruct R2 as [|A2 C2]; simpl in H; try discriminate.
  apply Bool.andb_true_iff in H as [Hleft Hright].
  apply Bool.andb_true_iff in Hleft as [HA1 HA2].
  apply Bool.andb_true_iff in Hright as [HB1 HC2].
  apply form_eqb_true_eq in HA1; subst A1.
  apply form_eqb_true_eq in HA2; subst A2.
  apply form_eqb_true_eq in HB1; subst B1.
  apply form_eqb_true_eq in HC2; subst C2.
  apply Ax_S.
Qed.

Lemma is_axiom_sound : forall phi, is_axiom phi = true -> Ax phi.
Proof.
  intros phi H.
  unfold is_axiom in H.
  apply Bool.orb_true_iff in H as [HE|Hrest].
  - apply is_EFQ_sound. exact HE.
  - apply Bool.orb_true_iff in Hrest as [HK|HS].
    + apply is_K_sound. exact HK.
    + apply is_S_sound. exact HS.
Qed.