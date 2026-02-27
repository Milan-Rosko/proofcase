(* R20__Aggregated_Evaluator.v *)

From Coq Require Import Arith List Lia PeanoNat.
Import ListNotations.

From T002 Require Import
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R11__Constraints_Assembly
  R13__Kernel_API
  R22__Channel_Bounds.

Definition eval_agg (pf : Proof) (target : Form) (a : Assignment) : nat :=
  if Nat.eqb (poly_eval (fst (emit_single_cubic pf target)) a)
             (poly_eval (snd (emit_single_cubic pf target)) a)
  then 0 else 1.

Definition AggSat (pf : Proof) (target : Form) : Prop :=
  exists a,
    as_pf a = pf /\
    as_target a = target /\
    eval_agg pf target a = 0.

Theorem aggregation_correct :
  forall base pf target,
    base > channel_bound_M ->
    CubicWitness pf target <-> AggSat pf target.
Proof.
  intros base pf target Hbase.
  split.
  - intros [a [Hpf [Htarget Heq]]].
    exists a.
    repeat split; try assumption.
    unfold eval_agg.
    unfold equation_holds in Heq.
    rewrite Heq.
    now rewrite Nat.eqb_refl.
  - intros [a [Hpf [Htarget Hagg]]].
    exists a.
    repeat split; try assumption.
    unfold equation_holds.
    unfold eval_agg in Hagg.
    destruct (Nat.eqb (poly_eval (fst (emit_single_cubic pf target)) a)
                      (poly_eval (snd (emit_single_cubic pf target)) a)) eqn:Heqb.
    { apply Nat.eqb_eq in Heqb. exact Heqb. }
    { simpl in Hagg. discriminate. }
Qed.
