(* R00__Degree_Framework.v *)

From Coq Require Import Arith Lia.

Inductive Expr : Type :=
  | Const : nat -> Expr
  | Var : nat -> Expr
  | Add : Expr -> Expr -> Expr
  | Sub : Expr -> Expr -> Expr
  | Mul : Expr -> Expr -> Expr.

Fixpoint degree (e : Expr) : nat :=
  match e with
  | Const _ => 0
  | Var _ => 1
  | Add a b => Nat.max (degree a) (degree b)
  | Sub a b => Nat.max (degree a) (degree b)
  | Mul a b => degree a + degree b
  end.

Lemma degree_add :
  forall a b,
    degree (Add a b) <= Nat.max (degree a) (degree b).
Proof.
  intros a b.
  simpl.
  lia.
Qed.

Lemma degree_sub :
  forall a b,
    degree (Sub a b) <= Nat.max (degree a) (degree b).
Proof.
  intros a b.
  simpl.
  lia.
Qed.

Lemma degree_mul :
  forall a b,
    degree (Mul a b) = degree a + degree b.
Proof.
  reflexivity.
Qed.

Lemma degree_square :
  forall a,
    degree (Mul a a) = 2 * degree a.
Proof.
  intro a.
  rewrite degree_mul.
  lia.
Qed.

Lemma degree_le_mul :
  forall a b k l,
    degree a <= k ->
    degree b <= l ->
    degree (Mul a b) <= k + l.
Proof.
  intros a b k l Ha Hb.
  rewrite degree_mul.
  lia.
Qed.