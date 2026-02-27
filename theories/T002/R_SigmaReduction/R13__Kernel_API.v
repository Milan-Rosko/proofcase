(* R13__Kernel_API.v *)

From Coq Require Import List.
Import ListNotations.

From T002 Require Import
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R09__Constraints_MP
  R11__Constraints_Assembly
  R12__Aggregation_Fib_Banded_Equality.

Definition checker : Proof -> Form -> bool :=
  check.

Definition cubic_accepts : Proof -> Form -> bool :=
  checker.

Definition canonical_assignment (pf : Proof) (target : Form) : Assignment :=
  {| as_pf := pf;
     as_target := target;
     as_c := 0;
     as_d := 0 |}.

Definition emit_cubic_system (pf : Proof) (target : Form) : list Polynomial :=
  polynomial_system (canonical_assignment pf target).

Definition emit_single_cubic (pf : Proof) (target : Form) : Polynomial * Polynomial :=
  banded_single_equation_for_system (emit_cubic_system pf target).

Definition compile (pf : Proof) (target : Form) : list Polynomial :=
  emit_cubic_system pf target.

Definition all_zero (sys : list Polynomial) (a : Assignment) : Prop :=
  forall p, In p sys -> poly_eval p a = 0.

Definition equation_holds (eqn : Polynomial * Polynomial) (a : Assignment) : Prop :=
  poly_eval (fst eqn) a = poly_eval (snd eqn) a.

Definition CubicWitness (pf : Proof) (target : Form) : Prop :=
  exists a,
    as_pf a = pf /\
    as_target a = target /\
    equation_holds (emit_single_cubic pf target) a.

Lemma system_constraints_pf_only :
  forall a1 a2,
    as_pf a1 = as_pf a2 ->
    system_constraints a1 = system_constraints a2.
Proof.
  intros a1 a2 Hpf.
  unfold system_constraints.
  now rewrite Hpf.
Qed.

Lemma polynomial_system_pf_only :
  forall a1 a2,
    as_pf a1 = as_pf a2 ->
    polynomial_system a1 = polynomial_system a2.
Proof.
  intros a1 a2 Hpf.
  unfold polynomial_system.
  now rewrite (system_constraints_pf_only a1 a2 Hpf).
Qed.

Lemma emit_single_cubic_pf_only :
  forall a pf target,
    as_pf a = pf ->
    emit_single_cubic pf target = banded_single_equation a.
Proof.
  intros a pf target Hpf.
  unfold emit_single_cubic, banded_single_equation, banded_single_equation_for_system.
  unfold emit_cubic_system.
  rewrite <- (polynomial_system_pf_only a (canonical_assignment pf target)).
  - reflexivity.
  - exact Hpf.
Qed.

Theorem cubic_accepts_iff_cubic_witness :
  forall pf target,
    cubic_accepts pf target = true <-> CubicWitness pf target.
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    apply (proj1 (proof_equiv_banded_single_equation pf target)) in Hcheck.
    destruct Hcheck as [a [Hpf [Htarget Hsingle]]].
    exists a.
    repeat split; try assumption.
    unfold equation_holds.
    rewrite (emit_single_cubic_pf_only a pf target Hpf).
    exact Hsingle.
  - intros [a [Hpf [Htarget Heq]]].
    apply (proj2 (proof_equiv_banded_single_equation pf target)).
    exists a.
    repeat split; try assumption.
    rewrite (emit_single_cubic_pf_only a pf target Hpf) in Heq.
    exact Heq.
Qed.

Theorem cubic_accepts_correct :
  forall pf target,
    cubic_accepts pf target = true ->
    CubicWitness pf target.
Proof.
  intros pf target Hacc.
  exact ((proj1 (cubic_accepts_iff_cubic_witness pf target)) Hacc).
Qed.

Theorem kernel_constraint_degree_le_3 :
  forall c,
    total_degree (poly_of_constraint c) <= 3.
Proof.
  exact poly_constraint_degree_le_3.
Qed.

Theorem kernel_system_degree_le_3 :
  forall a c,
    In c (system_constraints a) ->
    total_degree (poly_of_constraint c) <= 3.
Proof.
  exact constraints_degree_le_3.
Qed.

Theorem compiler_degree_bound :
  forall pf target,
    Forall (fun P => total_degree P <= 3)
           (emit_cubic_system pf target).
Proof.
  intros pf target.
  unfold emit_cubic_system.
  apply polynomial_system_forall_degree_le_3.
Qed.

Theorem degree_three_threshold :
  forall pf target,
    Forall (fun P => total_degree P <= 3)
           (compile pf target).
Proof.
  intros pf target.
  unfold compile.
  apply compiler_degree_bound.
Qed.

Theorem emit_single_cubic_degree_le_3 :
  forall pf target,
    total_degree (fst (emit_single_cubic pf target)) <= 3 /\
    total_degree (snd (emit_single_cubic pf target)) <= 3.
Proof.
  intros pf target.
  unfold emit_single_cubic.
  apply aggregate_banded_degree_le_3.
  unfold emit_cubic_system.
  apply polynomial_system_forall_degree_le_3.
Qed.

Theorem check_iff_emit_cubic_all_zero :
  forall pf target,
    check pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      all_zero (emit_cubic_system pf target) a.
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    destruct (proof_equiv_poly_zero pf target) as [Hforward _].
    specialize (Hforward Hcheck).
    destruct Hforward as [a [Hpf [Htarget Hzero]]].
    exists a.
    repeat split; try assumption.
    unfold all_zero.
    intros p Hp.
    unfold emit_cubic_system in Hp.
    rewrite <- (polynomial_system_pf_only a (canonical_assignment pf target)) in Hp.
    2:{ exact Hpf. }
    exact (Hzero p Hp).
  - intros [a [Hpf [Htarget Hall]]].
    destruct (proof_equiv_poly_zero pf target) as [_ Hback].
    apply Hback.
    exists a.
    repeat split; try assumption.
    intros p Hp.
    unfold all_zero in Hall.
    apply Hall.
    unfold emit_cubic_system.
    rewrite <- (polynomial_system_pf_only a (canonical_assignment pf target)).
    + exact Hp.
    + exact Hpf.
Qed.

Global Opaque cubic_accepts_iff_cubic_witness.
Global Opaque cubic_accepts_correct.
Global Opaque kernel_constraint_degree_le_3.
Global Opaque kernel_system_degree_le_3.
Global Opaque proof_equiv_agg_sum_zero.
Global Opaque proof_equiv_banded_single_equation.
Global Opaque proof_equiv_poly_zero.
Global Opaque constraint_poly_semantics.