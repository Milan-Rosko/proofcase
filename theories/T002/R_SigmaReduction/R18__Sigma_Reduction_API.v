(* R18__Sigma_Reduction_API.v *)

From Coq Require Import List Lia.
Import ListNotations.

From T002 Require Import
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R01__Foundation_Fibonacci
  R08__Constraints_Axiom
  R09__Constraints_MP
  R10__Constraints_Target
  R11__Constraints_Assembly
  R13__Kernel_API
  R14__Reduction_Core
  R15__Code_Bridge
  R16__Sigma_Reduction
  R20__Aggregated_Evaluator
  R22__Channel_Bounds.

Definition f : nat -> nat :=
  R16__Sigma_Reduction.f.

Definition Thm : nat -> Prop :=
  R16__Sigma_Reduction.Thm.

Definition CubicSat : nat -> Prop :=
  R16__Sigma_Reduction.CubicSat.

Definition eval_agg : Proof -> Form -> Assignment -> nat :=
  R20__Aggregated_Evaluator.eval_agg.

Definition AggSat : Proof -> Form -> Prop :=
  R20__Aggregated_Evaluator.AggSat.

Theorem aggregation_correct :
  forall base pf target,
    base > channel_bound_M ->
    CubicWitness pf target <-> AggSat pf target.
Proof.
  exact R20__Aggregated_Evaluator.aggregation_correct.
Qed.

Definition check_code : nat -> nat -> Prop :=
  R15__Code_Bridge.check_code.

Definition many_one_reduction
  (A B : nat -> Prop) (g : nat -> nat) : Prop :=
  R16__Sigma_Reduction.many_one_reduction A B g.

Definition many_one (A B : nat -> Prop) : Prop :=
  R16__Sigma_Reduction.many_one A B.

Definition primitive_recursive : (nat -> nat) -> Prop :=
  R16__Sigma_Reduction.primitive_recursive.

Definition DeciderCode : Type :=
  R16__Sigma_Reduction.DeciderCode.

Definition EvalRM (e input : nat) (b : bool) : Prop :=
  R16__Sigma_Reduction.EvalRM e input b.

Definition TotalRM (e : nat) : Prop :=
  R16__Sigma_Reduction.TotalRM e.

Definition toggle_code : nat -> nat :=
  R16__Sigma_Reduction.toggle_code.

Theorem sigma_reduction :
  forall u, Thm u <-> CubicSat (f u).
Proof.
  exact R16__Sigma_Reduction.sigma_reduction.
Qed.

Theorem CubicSat_semantic :
  forall n,
    CubicSat n <->
    exists pf target a,
      n = code_of_concrete pf target /\
      as_pf a = pf /\
      as_target a = target /\
      eval_agg pf target a = 0.
Proof.
  intro n.
  split.
  - intros [pf [target [Hn Hsat]]].
    exists pf, target.
    assert (Hbase : channel_bound_M + 1 > channel_bound_M) by lia.
    destruct (proj1 (aggregation_correct (channel_bound_M + 1) pf target Hbase) Hsat)
      as [a [Hpf [Htarget Hagg]]].
    exists a.
    repeat split; try assumption.
  - intros [pf [target [a [Hn [Hpf [Htarget Hagg]]]]]].
    exists pf, target.
    split; [exact Hn|].
    assert (Hbase : channel_bound_M + 1 > channel_bound_M) by lia.
    apply (proj2 (aggregation_correct (channel_bound_M + 1) pf target Hbase)).
    exists a.
    repeat split; try assumption.
Qed.

Theorem thm_iff_check_code :
  forall u, Thm u <-> exists p, check_code p u.
Proof.
  exact R16__Sigma_Reduction.thm_iff_check_code.
Qed.

Theorem thm_reduces_to_cubic :
  many_one Thm CubicSat.
Proof.
  exact R16__Sigma_Reduction.thm_reduces_to_cubic.
Qed.

Theorem compiler_primitive :
  primitive_recursive f.
Proof.
  exact R16__Sigma_Reduction.compiler_primitive.
Qed.

Theorem sigma1_hardness :
  exists g : nat -> nat,
    many_one_reduction Thm CubicSat g.
Proof.
  exact R16__Sigma_Reduction.sigma1_hardness.
Qed.

Theorem halting_reduces_to_thm :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> Thm (halt_to_thm x)) ->
    many_one Halting Thm.
Proof.
  exact R16__Sigma_Reduction.halting_reduces_to_thm.
Qed.

Theorem halting_reduces_to_cubic :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> Thm (halt_to_thm x)) ->
    many_one Halting CubicSat.
Proof.
  exact R16__Sigma_Reduction.halting_reduces_to_cubic.
Qed.

Theorem eval_rm_deterministic :
  forall e input b1 b2,
    EvalRM e input b1 ->
    EvalRM e input b2 ->
    b1 = b2.
Proof.
  intros e input b1 b2 H1 H2.
  exact (R16__Sigma_Reduction.EvalRM_deterministic e input b1 b2 H1 H2).
Qed.

Theorem eval_rm_total :
  forall e input, TotalRM e -> exists b, EvalRM e input b.
Proof.
  intros e input _.
  exists (R16__Sigma_Reduction.code_output e).
  unfold EvalRM.
  reflexivity.
Qed.

Theorem eval_rm_toggle_fixed_point :
  forall e input b,
    EvalRM (toggle_code e) input b <->
    EvalRM e (toggle_code e) (negb b).
Proof.
  exact R16__Sigma_Reduction.EvalRM_toggle_fixed_point.
Qed.

Theorem rm_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalRM q input b <->
        EvalRM e q (negb b).
Proof.
  exact R16__Sigma_Reduction.RM_recursion_theorem.
Qed.

Theorem source_toggle_point_exists :
  forall e : DeciderCode,
    exists u : nat, Thm u <-> EvalRM e (f u) false.
Proof.
  exact R16__Sigma_Reduction.source_toggle_point_exists.
Qed.

Theorem degree_three_threshold :
  forall u,
    Thm u ->
    exists pf target,
      f u = code_of_concrete pf target /\
      Forall (fun P => total_degree P <= 3) (compile pf target).
Proof.
  intros u Hu.
  destruct Hu as [pf [target [Hcode _]]].
  exists pf, target.
  split.
  - exact Hcode.
  - apply R13__Kernel_API.degree_three_threshold.
Qed.

(*************************************************************************)
(*                                                                       *)
(*  Numbered theorem aliases (stable paper-facing labels)                *)
(*                                                                       *)
(*************************************************************************)

Theorem SR01_sigma_reduction :
  forall u, Thm u <-> CubicSat (f u).
Proof.
  exact sigma_reduction.
Qed.

Theorem SR02_thm_reduces_to_cubic :
  many_one Thm CubicSat.
Proof.
  exact thm_reduces_to_cubic.
Qed.

Theorem SR03_compiler_primitive :
  primitive_recursive f.
Proof.
  exact compiler_primitive.
Qed.

Theorem SR04_sigma1_hardness :
  exists g : nat -> nat,
    many_one_reduction Thm CubicSat g.
Proof.
  exact sigma1_hardness.
Qed.

Theorem SR05_eval_rm_deterministic :
  forall e input b1 b2,
    EvalRM e input b1 ->
    EvalRM e input b2 ->
    b1 = b2.
Proof.
  exact eval_rm_deterministic.
Qed.

Theorem SR06_eval_rm_total :
  forall e input, TotalRM e -> exists b, EvalRM e input b.
Proof.
  exact eval_rm_total.
Qed.

Theorem SR07_eval_rm_toggle_fixed_point :
  forall e input b,
    EvalRM (toggle_code e) input b <->
    EvalRM e (toggle_code e) (negb b).
Proof.
  exact eval_rm_toggle_fixed_point.
Qed.

Theorem SR08_rm_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalRM q input b <->
        EvalRM e q (negb b).
Proof.
  exact rm_recursion_theorem.
Qed.

Global Opaque
  eval_rm_deterministic
  pair
  unpair
  P_axiom
  P_MP
  P_target
  constraint_poly_expr
  poly_of_constraint
  constraint_system
  emit_cubic_system
  emit_single_cubic
  compile.
