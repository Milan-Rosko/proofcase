(* P03__Undecidability.v *)

From T002 Require Import P00__Provability_Interface.
From T002 Require Import P05__Toggle_Contradiction.
From T002 Require Import P06__SourceToggle_Generator.

(*************************************************************************)
(*                                                                       *)
(*  Tier 2 endpoint over coded deciders                                  *)
(*                                                                       *)
(*************************************************************************)

Theorem no_total_correct_code_CubicSat :
  ~ exists e : DeciderCode, CorrectCode e.
Proof.
  intros [e He].
  apply (toggle_instance_contradiction_of_generator_code
           (toggle_witness_code_generator_from_source
              source_toggle_code_generator_internal)
           e
           He).
Qed.

Theorem no_total_correct_decider_CubicSat_computable :
  ~ exists D : Decider, Computable D /\ Correct D.
Proof.
  intros [D [Hcomp Hcorr]].
  destruct (computable_correct_implies_correct_code D Hcomp Hcorr) as [e He].
  apply no_total_correct_code_CubicSat.
  exists e.
  exact He.
Qed.

Theorem CubicSat_undecidable_code :
  ~ DecidableCode CubicSat.
Proof.
  intros [e [Htotal Hdec]].
  apply no_total_correct_code_CubicSat.
  exists e.
  split.
  - exact Htotal.
  - intro s.
    apply Hdec.
Qed.