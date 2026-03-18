(* R19__Sigma_Reduction_Minimal_API.v *)

From T002 Require Import R18__Sigma_Reduction_API.

Definition Thm : nat -> Prop :=
  R18__Sigma_Reduction_API.Thm.

Definition CubicSat : nat -> Prop :=
  R18__Sigma_Reduction_API.CubicSat.

Definition f : nat -> nat :=
  R18__Sigma_Reduction_API.f.

Definition check_code : nat -> nat -> Prop :=
  R18__Sigma_Reduction_API.check_code.

Definition many_one_reduction
  (A B : nat -> Prop) (g : nat -> nat) : Prop :=
  R18__Sigma_Reduction_API.many_one_reduction A B g.

Definition many_one (A B : nat -> Prop) : Prop :=
  R18__Sigma_Reduction_API.many_one A B.

Definition primitive_recursive : (nat -> nat) -> Prop :=
  R18__Sigma_Reduction_API.primitive_recursive.

Definition DeciderCode : Type :=
  R18__Sigma_Reduction_API.DeciderCode.

Definition EvalRM (e input : nat) (b : bool) : Prop :=
  R18__Sigma_Reduction_API.EvalRM e input b.

Definition TotalRM (e : nat) : Prop :=
  R18__Sigma_Reduction_API.TotalRM e.

Definition toggle_code : nat -> nat :=
  R18__Sigma_Reduction_API.toggle_code.

Theorem sigma_reduction :
  forall u, Thm u <-> CubicSat (f u).
Proof.
  exact R18__Sigma_Reduction_API.sigma_reduction.
Qed.

Theorem thm_iff_check_code :
  forall u, Thm u <-> exists p, check_code p u.
Proof.
  exact R18__Sigma_Reduction_API.thm_iff_check_code.
Qed.

Theorem thm_reduces_to_cubic :
  many_one Thm CubicSat.
Proof.
  exact R18__Sigma_Reduction_API.thm_reduces_to_cubic.
Qed.

Theorem compiler_primitive :
  primitive_recursive f.
Proof.
  exact R18__Sigma_Reduction_API.compiler_primitive.
Qed.

Theorem sigma1_hardness :
  exists g : nat -> nat,
    many_one_reduction Thm CubicSat g.
Proof.
  exact R18__Sigma_Reduction_API.sigma1_hardness.
Qed.

Theorem halting_reduces_to_thm :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> Thm (halt_to_thm x)) ->
    many_one Halting Thm.
Proof.
  exact R18__Sigma_Reduction_API.halting_reduces_to_thm.
Qed.

Theorem halting_reduces_to_cubic :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> Thm (halt_to_thm x)) ->
    many_one Halting CubicSat.
Proof.
  exact R18__Sigma_Reduction_API.halting_reduces_to_cubic.
Qed.

Theorem eval_rm_deterministic :
  forall e input b1 b2,
    EvalRM e input b1 ->
    EvalRM e input b2 ->
    b1 = b2.
Proof.
  exact R18__Sigma_Reduction_API.eval_rm_deterministic.
Qed.

Theorem eval_rm_total :
  forall e input, TotalRM e -> exists b, EvalRM e input b.
Proof.
  exact R18__Sigma_Reduction_API.eval_rm_total.
Qed.

Theorem eval_rm_toggle_fixed_point :
  forall e input b,
    EvalRM (toggle_code e) input b <->
    EvalRM e (toggle_code e) (negb b).
Proof.
  exact R18__Sigma_Reduction_API.eval_rm_toggle_fixed_point.
Qed.

Theorem rm_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalRM q input b <->
        EvalRM e q (negb b).
Proof.
  exact R18__Sigma_Reduction_API.rm_recursion_theorem.
Qed.

Theorem source_toggle_point_exists :
  forall e : DeciderCode,
    exists u : nat, Thm u <-> EvalRM e (f u) false.
Proof.
  exact R18__Sigma_Reduction_API.source_toggle_point_exists.
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

Global Opaque sigma_reduction.