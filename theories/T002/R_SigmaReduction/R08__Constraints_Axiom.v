(* R08__Axiom_Constraint.v *)

From Coq Require Import Arith List Bool PeanoNat Lia.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Export
  R06__Encoding_Formula_Coding.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker.

Record Assignment : Type := {
  as_pf : Proof;
  as_target : Form;
  as_c : nat;
  as_d : nat
}.

Inductive Constraint : Type :=
  | C_Axiom : nat -> Constraint
  | C_MP : nat -> nat -> nat -> Constraint
  | C_Justification : nat -> Constraint
  | C_Target : Constraint.

Definition P_axiom (_a : Assignment) (_i : nat) : Expr :=
  Mul (Var 0) (Var 1).

Theorem axiom_constraint_degree :
  forall a i,
    degree (P_axiom a i) <= 2.
Proof.
  intros a i.
  unfold P_axiom.
  rewrite degree_mul.
  simpl.
  lia.
Qed.

Global Opaque P_axiom.

Definition line_at (a : Assignment) (i : nat) : Form :=
  nth i (as_pf a) Bot.

Definition axiom_okb (a : Assignment) (i : nat) : bool :=
  andb (Nat.ltb i (length (as_pf a))) (is_axiom (line_at a i)).

Definition mp_okb (a : Assignment) (i j k : nat) : bool :=
  andb (Nat.ltb j i)
    (andb (Nat.ltb k i)
      (match line_at a k with
       | F_Imp x y => andb (form_eqb x (line_at a j)) (form_eqb y (line_at a i))
       | _ => false
       end)).

Definition justification_okb (a : Assignment) (i : nat) : bool :=
  andb (Nat.ltb i (length (as_pf a)))
       (check_lines [] (firstn (S i) (as_pf a))).

Definition target_okb (a : Assignment) : bool :=
  match last_opt (as_pf a) with
  | Some last => form_eqb last (as_target a)
  | None => false
  end.

Definition constraint_holdsb (a : Assignment) (c : Constraint) : bool :=
  match c with
  | C_Axiom i => axiom_okb a i
  | C_MP i j k => mp_okb a i j k
  | C_Justification i => justification_okb a i
  | C_Target => target_okb a
  end.

Definition constraint_holds (a : Assignment) (c : Constraint) : Prop :=
  constraint_holdsb a c = true.

Fixpoint satisfies (a : Assignment) (cs : list Constraint) : Prop :=
  match cs with
  | [] => True
  | c :: cs' => constraint_holds a c /\ satisfies a cs'
  end.

Lemma check_lines_firstn :
  forall ctx pf n,
    check_lines ctx pf = true ->
    check_lines ctx (firstn n pf) = true.
Proof.
  intros ctx pf n.
  revert ctx pf.
  induction n as [|n IH]; intros ctx pf H.
  - simpl. reflexivity.
  - destruct pf as [|line rest].
    + simpl. reflexivity.
    + simpl in H.
      apply Bool.andb_true_iff in H as [Hline Hrest].
      simpl.
      apply Bool.andb_true_iff.
      split.
      * exact Hline.
      * apply IH with (ctx := line :: ctx). exact Hrest.
Qed.

Lemma check_true_implies_target_ok :
  forall pf goal,
    check pf goal = true ->
    match last_opt pf with
    | Some last => form_eqb last goal = true
    | None => False
    end.
Proof.
  intros pf goal H.
  unfold check in H.
  destruct (last_opt pf) as [last|] eqn:Hlast.
  - apply Bool.andb_true_iff in H as [_ Hgoal].
    exact Hgoal.
  - discriminate.
Qed.