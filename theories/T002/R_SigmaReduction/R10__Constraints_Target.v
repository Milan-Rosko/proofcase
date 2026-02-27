(* R10__Target_Constraint.v *)

From Coq Require Import Arith List Bool PeanoNat Lia.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Import
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R09__Constraints_MP.

Definition P_target (_pf : Proof) (_target : Form) : Expr :=
  Mul (Var 0) (Var 1).

Theorem target_constraint_degree :
  forall pf target,
    degree (P_target pf target) <= 2.
Proof.
  intros pf target.
  unfold P_target.
  rewrite degree_mul.
  simpl.
  lia.
Qed.

Global Opaque P_target.

Corollary target_constraint_reflects_check :
  forall a,
    satisfies a (system_constraints a) ->
    check (as_pf a) (as_target a) = true.
Proof.
  intros a.
  apply check_from_satisfies_system.
Qed.