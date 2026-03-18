(* P00__Provability_Interface.v *)

From Coq Require Import Bool.

From T002 Require Import R19__Sigma_Reduction_Minimal_API.
From T002 Require Import P00__Concrete_Provability.

(*
  Provability: u is provable iff it has a coded proof witness.
*)

Definition Prov (u : nat) : Prop :=
  ProvCode u.

(*
  Theoremhood predicate re-exported from the sigma-reduction API.
*)

Definition Thm : nat -> Prop :=
  R19__Sigma_Reduction_Minimal_API.Thm.

(*
  Cubic satisfiability predicate.
*)

Definition CubicSat : nat -> Prop :=
  R19__Sigma_Reduction_Minimal_API.CubicSat.

(*
  The reduction map from theorem codes to cubic instances.
*)

Definition f : nat -> nat :=
  R19__Sigma_Reduction_Minimal_API.f.

(*
  A decider is a total boolean function on naturals.
*)

Definition Decider : Type := nat -> bool.

(*
  A decider code is a natural that indexes a coded decider.
*)

Definition DeciderCode : Type := T002.R19__Sigma_Reduction_Minimal_API.DeciderCode.

(*
  Evaluation of a coded decider on an input to a boolean result.
*)

Definition EvalCode (e input : nat) (b : bool) : Prop :=
  EvalRM e input b.

(*
  Totality of a coded decider: it halts on every input.
*)

Definition TotalCode (e : DeciderCode) : Prop :=
  TotalRM e.

(*
  Correctness of a coded decider for CubicSat.
*)

Definition CorrectCode (e : DeciderCode) : Prop :=
  TotalCode e /\ forall s, EvalCode e s true <-> CubicSat s.

(*
  Extensional correctness of a decider for CubicSat.
*)

Definition Correct (D : Decider) : Prop :=
  forall s, D s = true <-> CubicSat s.

(*
  A decider is computable iff it is realized by a total coded decider.
*)

Definition Computable (D : Decider) : Prop :=
  exists e : DeciderCode,
    TotalCode e /\ forall s, D s = true <-> EvalCode e s true.

(*
  A property is decidable iff some decider computes its characteristic.
*)

Definition Decidable (P : nat -> Prop) : Prop :=
  exists D : Decider, forall u, D u = true <-> P u.

(*
  A property is code-decidable iff some total coded decider computes it.
*)

Definition DecidableCode (P : nat -> Prop) : Prop :=
  exists e : DeciderCode, TotalCode e /\ forall u, EvalCode e u true <-> P u.

(*
  Coded evaluation is deterministic.
*)

Theorem EvalCode_deterministic :
  forall e input b1 b2,
    EvalCode e input b1 ->
    EvalCode e input b2 ->
    b1 = b2.
Proof.
  exact eval_rm_deterministic.
Qed.

(*
  A total coded decider produces a result on every input.
*)

Theorem EvalCode_total_input :
  forall e input, TotalCode e -> exists b, EvalCode e input b.
Proof.
  intros e input Htotal.
  exact (eval_rm_total e input Htotal).
Qed.

(*
  Toggle-code fixed-point: evaluating the toggle negates the result.
*)

Theorem EvalCode_toggle_fixed_point :
  forall e input b,
    EvalCode (toggle_code e) input b <->
    EvalCode e (toggle_code e) (negb b).
Proof.
  exact eval_rm_toggle_fixed_point.
Qed.

(*
  Recursion theorem: every code has a negation-fixed point.
*)

Theorem EvalCode_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalCode q input b <->
        EvalCode e q (negb b).
Proof.
  exact rm_recursion_theorem.
Qed.

(*
  Existence of a source-toggle fixed point for any coded decider.
*)

Theorem source_toggle_point_exists :
  forall e : DeciderCode,
    exists u : nat, Thm u <-> EvalCode e (f u) false.
Proof.
  exact R19__Sigma_Reduction_Minimal_API.source_toggle_point_exists.
Qed.

(*
  Provability and theoremhood coincide.
*)

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

(*
  Sigma reduction: provability reduces to cubic satisfiability.
*)

Theorem sigma_reduction_for_prov :
  forall u, Prov u <-> CubicSat (f u).
Proof.
  intros u.
  rewrite Prov_iff_Thm.
  apply sigma_reduction.
Qed.

(*
  A computable correct decider yields a correct coded decider.
*)

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