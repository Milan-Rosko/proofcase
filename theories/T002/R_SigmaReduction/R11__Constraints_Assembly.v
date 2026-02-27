(* R11__Assembly.v *)

From Coq Require Import Arith List Bool PeanoNat Lia.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Import
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R09__Constraints_MP
  R10__Constraints_Target.

Record Polynomial : Type := {
  poly_expr : Expr;
  poly_eval : Assignment -> nat
}.

Definition total_degree (p : Polynomial) : nat := degree (poly_expr p).

Definition bool_zero (b : bool) : nat := if b then 0 else 1.

Definition degree_witness_assignment : Assignment :=
  {| as_pf := [];
     as_target := F_Bot;
     as_c := 0;
     as_d := 0 |}.

Definition constraint_poly_expr (c : Constraint) : Expr :=
  match c with
  | C_Axiom i => P_axiom degree_witness_assignment i
  | C_MP i _ _ => P_MP degree_witness_assignment i
  | C_Justification i => P_MP degree_witness_assignment i
  | C_Target => P_target [] F_Bot
  end.

Definition poly_of_constraint (c : Constraint) : Polynomial :=
  {| poly_expr := constraint_poly_expr c;
     poly_eval := fun a => bool_zero (constraint_holdsb a c) |}.

Lemma bool_zero_eq_0_iff : forall b, bool_zero b = 0 <-> b = true.
Proof.
  destruct b; simpl; split; intro H; try reflexivity; discriminate.
Qed.

Theorem constraint_poly_semantics :
  forall a c,
    constraint_holds a c <-> poly_eval (poly_of_constraint c) a = 0.
Proof.
  intros a c.
  unfold constraint_holds, poly_of_constraint.
  simpl.
  rewrite bool_zero_eq_0_iff.
  tauto.
Qed.

Lemma poly_constraint_degree_le_3 :
  forall c, total_degree (poly_of_constraint c) <= 3.
Proof.
  intro c.
  unfold total_degree, poly_of_constraint, constraint_poly_expr.
  simpl.
  destruct c as [i|i j k|i|].
  - apply Nat.le_trans with (m := 2).
    + apply axiom_constraint_degree.
    + lia.
  - apply mp_constraint_degree.
  - apply mp_constraint_degree.
  - apply Nat.le_trans with (m := 2).
    + apply target_constraint_degree.
    + lia.
Qed.

Definition polynomial_system (a : Assignment) : list Polynomial :=
  map poly_of_constraint (system_constraints a).

Definition constraint_system (a : Assignment) : list Polynomial :=
  polynomial_system a.

Theorem constraints_degree_le_3 :
  forall a c,
    In c (system_constraints a) ->
    total_degree (poly_of_constraint c) <= 3.
Proof.
  intros a c _.
  apply poly_constraint_degree_le_3.
Qed.

Theorem assembly_degree :
  forall a P,
    In P (constraint_system a) ->
    total_degree P <= 3.
Proof.
  intros a P Hin.
  unfold constraint_system, polynomial_system in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [c [HP _]].
  subst P.
  apply poly_constraint_degree_le_3.
Qed.

Theorem polynomial_system_forall_degree_le_3 :
  forall a,
    Forall (fun P => total_degree P <= 3) (polynomial_system a).
Proof.
  intros a.
  apply Forall_forall.
  intros P HP.
  unfold constraint_system in *.
  apply (assembly_degree a P).
  exact HP.
Qed.

Theorem proof_equiv_sat_system :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      satisfies a (system_constraints a).
Proof.
  apply proof_equiv_sat.
Qed.

Theorem proof_equiv_poly_zero :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      (forall p, In p (polynomial_system a) -> poly_eval p a = 0).
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    destruct (proof_equiv_sat pf target) as [Hforward _].
    specialize (Hforward Hcheck).
    destruct Hforward as [a [Hpf [Htarget Hsat]]].
    exists a. repeat split; try assumption.
    intros p Hp.
    unfold polynomial_system in Hp.
    apply in_map_iff in Hp.
    destruct Hp as [c [Hp Hinc]].
    subst p.
    apply (proj1 (constraint_poly_semantics a c)).
    apply satisfies_in with (cs := system_constraints a).
    + exact Hsat.
    + exact Hinc.
  - intros [a [Hpf [Htarget Hzero]]].
    subst pf target.
    apply (proj2 (proof_equiv_sat_system (as_pf a) (as_target a))).
    exists a.
    split; [reflexivity|].
    split; [reflexivity|].
    apply satisfies_of_all.
    intros c Hc.
    apply (proj2 (constraint_poly_semantics a c)).
    apply Hzero.
    unfold polynomial_system.
    apply in_map_iff.
    exists c.
    split; [reflexivity|exact Hc].
Qed.