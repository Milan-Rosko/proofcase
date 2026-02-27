(* P05__Toggle_Contradiction.v *)

From T002 Require Import P00__Provability_Interface.

(*************************************************************************)
(*                                                                       *)
(*  Tier 2 toggle contradiction core (coded deciders only)               *)
(*                                                                       *)
(*************************************************************************)

Definition ToggleWitnessCode (e : DeciderCode) : Prop :=
  exists s : nat,
    CubicSat s <-> EvalCode e s false.

Definition ToggleWitnessCodeGenerator : Prop :=
  forall e : DeciderCode, ToggleWitnessCode e.

Definition SourceTogglePointCode (e : DeciderCode) (u : nat) : Prop :=
  Prov u <-> EvalCode e (f u) false.

Definition SourceToggleCodeGenerator : Prop :=
  forall e : DeciderCode, exists u : nat, SourceTogglePointCode e u.

Definition Toggle_Instance_Contradiction_Code : Prop :=
  forall e : DeciderCode, CorrectCode e -> False.

(* Bridge 1: source fixed-point over theorem codes yields cubic witness. *)
Theorem toggle_witness_code_from_source_point :
  forall e u,
    SourceTogglePointCode e u ->
    ToggleWitnessCode e.
Proof.
  intros e u Hsrc.
  exists (f u).
  rewrite <- sigma_reduction_for_prov.
  exact Hsrc.
Qed.

Theorem toggle_witness_code_generator_from_source :
  SourceToggleCodeGenerator ->
  ToggleWitnessCodeGenerator.
Proof.
  intros Hsrc e.
  destruct (Hsrc e) as [u Hu].
  apply (toggle_witness_code_from_source_point e u).
  exact Hu.
Qed.

Lemma eval_true_false_impossible :
  forall e s,
    EvalCode e s true ->
    EvalCode e s false ->
    False.
Proof.
  intros e s Ht Hf.
  pose proof (EvalCode_deterministic e s true false Ht Hf) as Heq.
  discriminate Heq.
Qed.

(* Bridge 2: one toggle witness for e collapses CorrectCode e. *)
Theorem toggle_witness_code_contradiction :
  forall e : DeciderCode,
    CorrectCode e ->
    ToggleWitnessCode e ->
    False.
Proof.
  intros e [Htotal Hcorr] [s Htoggle].
  specialize (Hcorr s).
  assert (Htf : EvalCode e s true -> EvalCode e s false).
  {
    intro Htrue.
    apply (proj1 Htoggle).
    apply (proj1 Hcorr).
    exact Htrue.
  }
  destruct (EvalCode_total_input e s Htotal) as [b Hb].
  destruct b.
  - apply (eval_true_false_impossible e s Hb (Htf Hb)).
  - pose proof (proj2 Htoggle Hb) as Hsat.
    pose proof (proj2 Hcorr Hsat) as Htrue.
    apply (eval_true_false_impossible e s Htrue Hb).
Qed.

Theorem toggle_instance_contradiction_of_generator_code :
  ToggleWitnessCodeGenerator ->
  Toggle_Instance_Contradiction_Code.
Proof.
  intros Hgen e Hcorr.
  apply (toggle_witness_code_contradiction e Hcorr).
  apply Hgen.
Qed.