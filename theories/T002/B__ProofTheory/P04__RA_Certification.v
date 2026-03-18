(* P04__RA_Certification.v *)

From T002 Require Import P00__Provability_Interface.
From T002 Require Import P03__Undecidability.

(*************************************************************************)
(*                                                                       *)
(*  Tier 3: Internal certification endpoint (coded deciders)             *)
(*                                                                       *)
(*************************************************************************)

Section Tier3.

Variable RA_Certified_DeciderCode : DeciderCode -> Prop.
Hypothesis RA_certified_sound :
  forall e, RA_Certified_DeciderCode e -> CorrectCode e.

Theorem no_RA_certified_decider_code :
  ~ exists e : DeciderCode, RA_Certified_DeciderCode e.
Proof.
  intros [e He].
  apply no_total_correct_code_CubicSat.
  exists e.
  apply RA_certified_sound.
  exact He.
Qed.

End Tier3.