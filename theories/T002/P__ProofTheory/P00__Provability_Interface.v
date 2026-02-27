(* P00__Provability_Interface.v *)

From Coq Require Import Bool.

From T002 Require Import R19__Sigma_Reduction_Minimal_API.
From T002 Require Import P00__Concrete_Provability.

Definition Prov (u : nat) : Prop :=
  ProvCode u.

Definition Thm : nat -> Prop :=
  R19__Sigma_Reduction_Minimal_API.Thm.

Definition CubicSat : nat -> Prop :=
  R19__Sigma_Reduction_Minimal_API.CubicSat.

Definition f : nat -> nat :=
  R19__Sigma_Reduction_Minimal_API.f.

Definition Decider : Type := nat -> bool.

Definition DeciderCode : Type := T002.R19__Sigma_Reduction_Minimal_API.DeciderCode.

Definition EvalCode (e input : nat) (b : bool) : Prop :=
  EvalRM e input b.

Definition TotalCode (e : DeciderCode) : Prop :=
  TotalRM e.

Definition CorrectCode (e : DeciderCode) : Prop :=
  TotalCode e /\ forall s, EvalCode e s true <-> CubicSat s.

Definition Correct (D : Decider) : Prop :=
  forall s, D s = true <-> CubicSat s.

Definition Computable (D : Decider) : Prop :=
  exists e : DeciderCode,
    TotalCode e /\ forall s, D s = true <-> EvalCode e s true.

Definition Decidable (P : nat -> Prop) : Prop :=
  exists D : Decider, forall u, D u = true <-> P u.

Definition DecidableCode (P : nat -> Prop) : Prop :=
  exists e : DeciderCode, TotalCode e /\ forall u, EvalCode e u true <-> P u.

Theorem EvalCode_deterministic :
  forall e input b1 b2,
    EvalCode e input b1 ->
    EvalCode e input b2 ->
    b1 = b2.
Proof.
  exact eval_rm_deterministic.
Qed.

Theorem EvalCode_total_input :
  forall e input, TotalCode e -> exists b, EvalCode e input b.
Proof.
  intros e input Htotal.
  exact (eval_rm_total e input Htotal).
Qed.

Theorem EvalCode_toggle_fixed_point :
  forall e input b,
    EvalCode (toggle_code e) input b <->
    EvalCode e (toggle_code e) (negb b).
Proof.
  exact eval_rm_toggle_fixed_point.
Qed.

Theorem EvalCode_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalCode q input b <->
        EvalCode e q (negb b).
Proof.
  exact rm_recursion_theorem.
Qed.

Theorem source_toggle_point_exists :
  forall e : DeciderCode,
    exists u : nat, Thm u <-> EvalCode e (f u) false.
Proof.
  exact R19__Sigma_Reduction_Minimal_API.source_toggle_point_exists.
Qed.

Theorem Prov_iff_Thm :
  forall u, Prov u <-> Thm u.
Proof.
  intros u.
  unfold Prov, ProvCode, Concrete_Proof, Thm.
  split.
  - intros [p [pf [target [_ [Hu Hcheck]]]]].
    exists pf, target.
    split; assumption.
  - intros [pf [target [Hu Hcheck]]].
    rewrite Hu.
    apply checker_accepts_implies_ProvCode.
    exact Hcheck.
Qed.

Theorem sigma_reduction_for_prov :
  forall u, Prov u <-> CubicSat (f u).
Proof.
  intros u.
  rewrite Prov_iff_Thm.
  apply sigma_reduction.
Qed.

Theorem computable_correct_implies_correct_code :
  forall D,
    Computable D ->
    Correct D ->
    exists e, CorrectCode e.
Proof.
  intros D [e [Htotal He]] Hcorr.
  exists e.
  split.
  - exact Htotal.
  - intro s.
    split.
    + intro Hev.
      apply (proj1 (Hcorr s)).
      apply (proj2 (He s)).
      exact Hev.
    + intro Hsat.
      apply (proj1 (He s)).
      apply (proj2 (Hcorr s)).
      exact Hsat.
Qed.