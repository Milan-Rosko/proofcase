(* R04__1st_Corollary.v *)

From T004 Require Import R03__Phase_Three.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 First Corollary Layer                            *)
(*                                                                       *)
(*  Consolidated external corollary layer.  This file does not add new   *)
(*  internal combinatorics; it packages the exact external consequence   *)
(*  of the remaining semantic premise classical_semantic_faithfulness.   *)
(*                                                                       *)
(*  The route has three steps.                                           *)
(*                                                                       *)
(*    1. Accept faithful outward window growth as an external semantic   *)
(*       premise.                                                        *)
(*                                                                       *)
(*    2. Convert that premise to the BHK-style window-upgrade principle  *)
(*       provided by Phase 3.                                            *)
(*                                                                       *)
(*    3. Apply the Phase 3 impossibility theorems to rule out            *)
(*       observational periodic tails and hence eventual periodic        *)
(*       centered windows.                                               *)
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

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Classical Semantics Excludes Eventual Periodic Windows             *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    A. Assume classical_semantic_faithfulness, i.e. faithful outward   *)
(*       growth for observational periodic tails.                        *)
(*                                                                       *)
(*    B. Convert that premise to bhk_window_upgrade_principle.           *)
(*                                                                       *)
(*    C. Invoke the packaged Phase 3 corollary that any fixed-radius     *)
(*       eventual periodic window is impossible under that upgrade.      *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    classical_semantic_faithfulness ->                                 *)
(*      forall R, ~ eventually_periodic_center_window R                  *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    If one accepts faithful outward Rule 30 window semantics, then     *)
(*    no centered observation radius of the seeded orbit can become      *)
(*    eventually periodic.                                               *)
(*                                                                       *)
(*************************************************************************)

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

End Classic_Semantics.
