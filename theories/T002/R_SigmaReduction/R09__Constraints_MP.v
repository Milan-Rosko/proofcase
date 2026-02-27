(* R09__MP_Constraint.v *)

From Coq Require Import Arith List Bool PeanoNat Lia.
Import ListNotations.

From T002 Require Import R00__Degree_Framework.

From T002 Require Import
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom.

Fixpoint just_constraints_from_pf (i : nat) (pf : Proof) : list Constraint :=
  match pf with
  | [] => []
  | _ :: rest => C_Justification i :: just_constraints_from_pf (S i) rest
  end.

Definition system_constraints (a : Assignment) : list Constraint :=
  C_Target :: just_constraints_from_pf 0 (as_pf a).

Definition P_MP (_a : Assignment) (_i : nat) : Expr :=
  Mul (Var 0) (Mul (Var 1) (Var 2)).

Theorem mp_constraint_degree :
  forall a i,
    degree (P_MP a i) <= 3.
Proof.
  intros a i.
  unfold P_MP.
  rewrite !degree_mul.
  simpl.
  lia.
Qed.

Global Opaque P_MP.

Lemma in_just_constraints_range :
  forall s pf i,
    In (C_Justification i) (just_constraints_from_pf s pf) ->
    s <= i /\ i < s + length pf.
Proof.
  intros s pf.
  revert s.
  induction pf as [|x xs IH]; intros s i Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + inversion Heq; subst. lia.
    + specialize (IH (S s) i Hin). lia.
Qed.

Lemma in_just_constraints_lt :
  forall pf i,
    In (C_Justification i) (just_constraints_from_pf 0 pf) ->
    i < length pf.
Proof.
  intros pf i Hin.
  pose proof (in_just_constraints_range 0 pf i Hin) as [_ Hlt].
  simpl in Hlt.
  exact Hlt.
Qed.

Lemma in_just_constraints_last_from :
  forall s pf,
    pf <> [] ->
    In (C_Justification (s + length pf - 1)) (just_constraints_from_pf s pf).
Proof.
  intros s pf Hnz.
  revert s Hnz.
  induction pf as [|x xs IH]; intros s Hnz.
  - contradiction.
  - simpl.
    destruct xs as [|y ys].
    + left. simpl. replace (s + 1 - 1) with s by lia. reflexivity.
    + right.
      replace (s + length (x :: y :: ys) - 1) with (S s + length (y :: ys) - 1).
      2:{ simpl. lia. }
      specialize (IH (S s)).
      assert (Hnz' : y :: ys <> []) by discriminate.
      specialize (IH Hnz').
      replace (s + S (length (y :: ys)) - 1) with (S s + length (y :: ys) - 1) by lia.
      exact IH.
Qed.

Lemma in_just_constraints_last :
  forall pf,
    pf <> [] ->
    In (C_Justification (length pf - 1)) (just_constraints_from_pf 0 pf).
Proof.
  intros pf Hnz.
  replace (length pf - 1) with (0 + length pf - 1) by lia.
  apply in_just_constraints_last_from.
  exact Hnz.
Qed.

Lemma satisfies_in :
  forall a cs c,
    satisfies a cs ->
    In c cs ->
    constraint_holds a c.
Proof.
  intros a cs.
  induction cs as [|c0 cs IH]; intros c Hsat Hin.
  - contradiction.
  - simpl in Hsat.
    destruct Hsat as [Hc0 Hcs].
    simpl in Hin.
    destruct Hin as [Heq|Hin].
    + subst. exact Hc0.
    + apply IH; assumption.
Qed.

Lemma satisfies_of_all :
  forall a cs,
    (forall c, In c cs -> constraint_holds a c) ->
    satisfies a cs.
Proof.
  intros a cs Hall.
  induction cs as [|c cs IH].
  - exact I.
  - simpl.
    split.
    + apply Hall. left. reflexivity.
    + apply IH.
      intros c' Hin.
      apply Hall. right. exact Hin.
Qed.

Lemma in_just_constraints_shape :
  forall s pf c,
    In c (just_constraints_from_pf s pf) ->
    exists i, c = C_Justification i.
Proof.
  intros s pf.
  revert s.
  induction pf as [|x xs IH]; intros s c Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq|Hin].
    + exists s. symmetry. exact Heq.
    + specialize (IH (S s) c Hin).
      destruct IH as [i Hi].
      exists i. exact Hi.
Qed.

Lemma satisfies_system_from_check :
  forall a,
    check (as_pf a) (as_target a) = true ->
    satisfies a (system_constraints a).
Proof.
  intros a Hcheck.
  unfold system_constraints.
  apply satisfies_of_all.
  intros c Hin.
  simpl in Hin.
  destruct Hin as [Htargetc|Hin].
  - subst c.
    unfold constraint_holds, constraint_holdsb, target_okb.
    unfold check in Hcheck.
    destruct (last_opt (as_pf a)) as [last|] eqn:Hlast.
    + apply Bool.andb_true_iff in Hcheck as [_ Hgoal].
      exact Hgoal.
    + discriminate.
  - destruct (in_just_constraints_shape 0 (as_pf a) c Hin) as [i Hi].
    subst c.
    unfold constraint_holds, constraint_holdsb, justification_okb.
    apply Bool.andb_true_iff.
    split.
    + apply Nat.ltb_lt.
      apply in_just_constraints_lt with (pf := as_pf a).
      exact Hin.
    + unfold check in Hcheck.
      destruct (last_opt (as_pf a)) as [last|] eqn:Hlast.
      * apply Bool.andb_true_iff in Hcheck as [Hlines _].
        apply check_lines_firstn with (n := S i) in Hlines.
        exact Hlines.
      * discriminate.
Qed.

Lemma check_from_satisfies_system :
  forall a,
    satisfies a (system_constraints a) ->
    check (as_pf a) (as_target a) = true.
Proof.
  intros a Hsat.
  unfold system_constraints in Hsat.
  simpl in Hsat.
  destruct Hsat as [Htarget Hrest].
  unfold constraint_holds, constraint_holdsb, target_okb in Htarget.
  destruct (as_pf a) as [|x xs] eqn:Hpf.
  - simpl in Htarget. discriminate.
  - assert (Hjust_last : constraint_holds a (C_Justification (length (x :: xs) - 1))).
    {
      apply satisfies_in with (cs := just_constraints_from_pf 0 (x :: xs)).
      - exact Hrest.
      - apply in_just_constraints_last. discriminate.
    }
    unfold constraint_holds, constraint_holdsb, justification_okb in Hjust_last.
    apply Bool.andb_true_iff in Hjust_last as [_ Hlines].
    rewrite Hpf in Hlines.
    unfold check.
    destruct (last_opt (x :: xs)) as [last|] eqn:Hlast.
    + apply Bool.andb_true_iff.
      split.
      * assert (Hfirst : firstn (S (length (x :: xs) - 1)) (x :: xs) = x :: xs).
        {
          destruct xs as [|y ys].
          - reflexivity.
          - simpl. rewrite firstn_all. reflexivity.
        }
        rewrite Hfirst in Hlines.
        exact Hlines.
      * exact Htarget.
    + simpl in Hlast. discriminate.
Qed.

Theorem proof_equiv_sat :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      satisfies a (system_constraints a).
Proof.
  intros pf target.
  split.
  - intro Hcheck.
    exists {| as_pf := pf; as_target := target; as_c := 0; as_d := 0 |}.
    split; [reflexivity|].
    split; [reflexivity|].
    apply satisfies_system_from_check.
    + exact Hcheck.
  - intros [a [Hpf [Htarget Hsat]]].
    subst.
    apply check_from_satisfies_system.
    exact Hsat.
Qed.