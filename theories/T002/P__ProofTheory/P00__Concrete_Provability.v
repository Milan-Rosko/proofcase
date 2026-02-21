(* P00__Concrete_Provability.v *)

From Coq Require Import Arith Bool Lia.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R06__Encoding_Formula_Coding
  R15__Code_Bridge.

Definition Concrete_Proof (p u : nat) : Prop :=
  check_code p u.

Lemma Concrete_Proof_unfold :
  forall p u,
    Concrete_Proof p u <->
    exists pf target,
      p = code_pf pf /\
      u = code_of_concrete pf target /\
      check pf target = true.
Proof.
  intros p u.
  unfold Concrete_Proof.
  apply check_code_unfold.
Qed.

Definition ProvCode (u : nat) : Prop :=
  exists p, Concrete_Proof p u.

Lemma checker_accepts_implies_ProvCode :
  forall pf target,
    check pf target = true ->
    ProvCode (code_of_concrete pf target).
Proof.
  intros pf target Hcheck.
  exists (code_pf pf).
  unfold Concrete_Proof, check_code.
  exists pf, target.
  repeat split; try reflexivity.
  exact Hcheck.
Qed.

Inductive OForm : Type :=
| O_Bot : OForm
| O_Imp : OForm -> OForm -> OForm
| O_Hole : OForm.

Fixpoint osize (phi : OForm) : nat :=
  match phi with
  | O_Bot => 1
  | O_Hole => 1
  | O_Imp a b => S (osize a + osize b)
  end.

Section SubstitutionCodes.

Variable hole_code : nat.

Fixpoint enc_oform (phi : OForm) : nat :=
  match phi with
  | O_Bot => 0
  | O_Imp a b => S (pair P0 (enc_oform a) (enc_oform b))
  | O_Hole => hole_code
  end.

Inductive OShape : Type :=
| ShBot : OShape
| ShImp : nat -> nat -> OShape
| ShHole : OShape.

Definition decode_oform1 (n : nat) : OShape :=
  if Nat.eqb n hole_code then ShHole
  else
    match n with
    | 0 => ShBot
    | S k =>
        let '(x, y) := unpair P0 k in
        ShImp x y
    end.

Fixpoint subst_code_fuel (fuel n t : nat) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match decode_oform1 n with
      | ShBot => 0
      | ShHole => t
      | ShImp a b =>
          S (pair P0 (subst_code_fuel fuel' a t)
                     (subst_code_fuel fuel' b t))
      end
  end.

Definition subst_code (n t : nat) : nat :=
  subst_code_fuel (S n) n t.

Fixpoint subst_oform (phi : OForm) (t : nat) : nat :=
  match phi with
  | O_Bot => 0
  | O_Imp a b => S (pair P0 (subst_oform a t) (subst_oform b t))
  | O_Hole => t
  end.

Definition ClosedCode (n : nat) : Prop :=
  exists psi : Form, enc_form psi = n.

Fixpoint close_oform (phi : OForm) (theta : Form) : Form :=
  match phi with
  | O_Bot => F_Bot
  | O_Imp a b => F_Imp (close_oform a theta) (close_oform b theta)
  | O_Hole => theta
  end.

Lemma close_oform_enc :
  forall phi theta,
    enc_form (close_oform phi theta) = subst_oform phi (enc_form theta).
Proof.
  induction phi as [|a IHa b IHb|]; intro theta; simpl.
  - reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - reflexivity.
Qed.

Lemma subst_oform_preserves_closed :
  forall phi t,
    ClosedCode t ->
    ClosedCode (subst_oform phi t).
Proof.
  intros phi t [theta Htheta].
  exists (close_oform phi theta).
  rewrite close_oform_enc.
  now rewrite Htheta.
Qed.

Section Correctness.

Hypothesis unpair_pair_P0 :
  forall a b, unpair P0 (pair P0 a b) = (a, b).

Hypothesis hole_code_not_bot :
  hole_code <> 0.

Hypothesis hole_code_fresh :
  forall a b, hole_code <> S (pair P0 a b).

Lemma decode_oform1_enc_bot :
  decode_oform1 (enc_oform O_Bot) = ShBot.
Proof.
  unfold decode_oform1, enc_oform.
  destruct (Nat.eqb_spec 0 hole_code) as [H0|H0].
  - exfalso. apply hole_code_not_bot. symmetry. exact H0.
  - reflexivity.
Qed.

Lemma decode_oform1_enc_hole :
  decode_oform1 (enc_oform O_Hole) = ShHole.
Proof.
  unfold decode_oform1, enc_oform.
  now rewrite Nat.eqb_refl.
Qed.

Lemma decode_oform1_enc_imp :
  forall a b,
    decode_oform1 (enc_oform (O_Imp a b)) = ShImp (enc_oform a) (enc_oform b).
Proof.
  intros a b.
  unfold decode_oform1.
  cbn [enc_oform].
  destruct (Nat.eqb_spec (S (pair P0 (enc_oform a) (enc_oform b))) hole_code) as [Heq|Hneq].
  - exfalso. apply (hole_code_fresh (enc_oform a) (enc_oform b)).
    symmetry. exact Heq.
  - rewrite unpair_pair_P0.
    reflexivity.
Qed.

Lemma subst_code_fuel_correct :
  forall fuel phi t,
    osize phi <= fuel ->
    subst_code_fuel fuel (enc_oform phi) t = subst_oform phi t.
Proof.
  induction fuel as [|fuel IH]; intros phi t Hsz.
  - destruct phi; simpl in Hsz; lia.
  - destruct phi as [|a b|].
    + cbn [enc_oform subst_oform].
      unfold subst_code_fuel at 1.
      fold subst_code_fuel.
      change (decode_oform1 0) with (decode_oform1 (enc_oform O_Bot)).
      rewrite decode_oform1_enc_bot.
      reflexivity.
    + simpl in Hsz.
      cbn [enc_oform subst_oform].
      unfold subst_code_fuel at 1.
      fold subst_code_fuel.
      change (decode_oform1 (S (pair P0 (enc_oform a) (enc_oform b))))
        with (decode_oform1 (enc_oform (O_Imp a b))).
      rewrite decode_oform1_enc_imp.
      f_equal.
      apply f_equal2.
      * apply IH. lia.
      * apply IH. lia.
    + cbn [enc_oform subst_oform].
      unfold subst_code_fuel at 1.
      fold subst_code_fuel.
      change (decode_oform1 hole_code) with (decode_oform1 (enc_oform O_Hole)).
      rewrite decode_oform1_enc_hole.
      reflexivity.
Qed.

Theorem subst_code_correct :
  forall phi t,
    subst_code_fuel (osize phi) (enc_oform phi) t = subst_oform phi t.
Proof.
  intros phi t.
  apply subst_code_fuel_correct.
  lia.
Qed.

Theorem subst_code_preserves_closed :
  forall phi t,
    ClosedCode t ->
    ClosedCode (subst_code_fuel (osize phi) (enc_oform phi) t).
Proof.
  intros phi t Ht.
  rewrite subst_code_correct.
  apply subst_oform_preserves_closed.
  exact Ht.
Qed.

End Correctness.

End SubstitutionCodes.