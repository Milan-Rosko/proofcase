(* R22__Channel_Bounds.v *)

From Coq Require Import Arith List Lia PeanoNat.
Import ListNotations.

From T002 Require Import
  R02__Foundation_Zeckendorf
  R08__Constraints_Axiom
  R11__Constraints_Assembly
  R12__Aggregation_Fib_Banded_Equality
  R13__Kernel_API.

Definition digit_value (a : Assignment) (i : nat) : nat :=
  match nth_error (split_channels (polynomial_system a)) i with
  | Some C => poly_eval C a
  | None => 0
  end.

Lemma digit_nonneg :
  forall a i, 0 <= digit_value a i.
Proof.
  intros a i.
  unfold digit_value.
  destruct (nth_error (split_channels (polynomial_system a)) i); lia.
Qed.

Definition channel_bound_M : nat := capacity_bound band_width - 1.

Lemma channel_bound_M_eq :
  channel_bound_M = 4.
Proof.
  unfold channel_bound_M, capacity_bound, band_width, Fib.
  vm_compute.
  reflexivity.
Qed.

Lemma lt_capacity_bound_implies_le_M :
  forall x,
    x < capacity_bound band_width ->
    x <= channel_bound_M.
Proof.
  intros x Hx.
  unfold channel_bound_M, capacity_bound in *.
  pose proof (F_pos_S band_width) as Hpos.
  lia.
Qed.

Lemma digit_value_bound_for_system :
  forall a i,
    (forall p, In p (polynomial_system a) -> poly_eval p a = 0) ->
    digit_value a i <= channel_bound_M.
Proof.
  intros a i Hsys.
  unfold digit_value.
  destruct (nth_error (split_channels (polynomial_system a)) i) as [C|] eqn:Hnth.
  - assert (Hin : In C (split_channels (polynomial_system a))).
    { eapply nth_error_In; eauto. }
    apply lt_capacity_bound_implies_le_M.
    eapply satisfies_system_implies_channel_bounds; eauto.
  - lia.
Qed.

Lemma digit_value_bound_for_equation :
  forall pf target a i,
    as_pf a = pf ->
    as_target a = target ->
    equation_holds (emit_single_cubic pf target) a ->
    digit_value a i <= channel_bound_M.
Proof.
  intros pf target a i Hpf Htarget Heq.
  unfold equation_holds in Heq.
  rewrite (emit_single_cubic_pf_only a pf target Hpf) in Heq.
  unfold banded_single_equation, banded_single_equation_for_system in Heq.
  apply digit_value_bound_for_system.
  apply (proj2 (single_equation_correct band_width (polynomial_system a) a)).
  exact Heq.
Qed.

Lemma digit_bound :
  exists M,
  forall pf target a i,
    as_pf a = pf ->
    as_target a = target ->
    equation_holds (emit_single_cubic pf target) a ->
    digit_value a i <= M.
Proof.
  exists channel_bound_M.
  intros pf target a i Hpf Htarget Heq.
  eapply digit_value_bound_for_equation; eauto.
Qed.

Definition aggregation_complete (base : nat) : Prop :=
  forall pf target a i,
    as_pf a = pf ->
    as_target a = target ->
    equation_holds (emit_single_cubic pf target) a ->
    digit_value a i < base.

Lemma base_sufficient :
  forall base,
    base > channel_bound_M ->
    aggregation_complete base.
Proof.
  intros base Hbase pf target a i Hpf Htarget Heq.
  pose proof (digit_value_bound_for_equation pf target a i Hpf Htarget Heq) as Hbound.
  lia.
Qed.
