(* R07__Classic_Semantics.v *)

From T004 Require Import R06__Mixed_Periodicity.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 3 -- Classical semantic corollaries        *)
(*                                                                       *)
(*  This file does not add a new proof engine.  It packages the exact    *)
(*  consequence of the one remaining semantic premise: faithful          *)
(*  Rule 30 window semantics should grow the observable window by one    *)
(*  at each backward semantic step.                                      *)
(*                                                                       *)
(*************************************************************************)

Section Classic_Semantics.

Definition classical_semantic_faithfulness : Prop :=
  faithful_window_growth_principle.

Theorem classical_semantic_faithfulness_implies_bhk_upgrade :
  classical_semantic_faithfulness ->
  bhk_window_upgrade_principle.
Proof.
  exact faithful_window_growth_implies_bhk_window_upgrade.
Qed.

Theorem classical_semantics_excludes_observational_periodic_tails :
  classical_semantic_faithfulness ->
  forall R T P,
    ~ observational_periodic_tail_from R T P.
Proof.
  intros Hfaith R T P Hobs.
  eapply observational_periodic_tail_from_impossible_under_bhk_upgrade.
  - exact (classical_semantic_faithfulness_implies_bhk_upgrade Hfaith).
  - exact Hobs.
Qed.

Theorem classical_semantics_excludes_eventual_periodic_windows :
  classical_semantic_faithfulness ->
  forall R,
    ~ eventually_periodic_center_window R.
Proof.
  intros Hfaith R.
  apply eventually_periodic_center_window_impossible_under_bhk_upgrade.
  exact (classical_semantic_faithfulness_implies_bhk_upgrade Hfaith).
Qed.

Theorem classical_semantics_excludes_any_eventual_periodic_window :
  classical_semantic_faithfulness ->
  ~ exists R, eventually_periodic_center_window R.
Proof.
  intros Hfaith [R Hobs].
  exact (classical_semantics_excludes_eventual_periodic_windows Hfaith R Hobs).
Qed.

Theorem faithful_observational_realizers_already_impossible :
  forall R,
    ~ realizable_observational_periodic_tail_from R.
Proof.
  exact realizable_observational_periodic_tail_from_impossible.
Qed.

Theorem faithful_uniform_realizers_already_impossible :
  forall R,
    ~ realizable_uniform_periodic_tail_from R.
Proof.
  exact realizable_uniform_periodic_tail_from_impossible.
Qed.

End Classic_Semantics.
