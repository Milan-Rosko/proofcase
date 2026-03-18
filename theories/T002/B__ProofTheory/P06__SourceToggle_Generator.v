(* P06__SourceToggle_Generator.v *)

From T002 Require Import P00__Provability_Interface.
From T002 Require Import P05__Toggle_Contradiction.

(*************************************************************************)
(*                                                                       *)
(*  Internal source toggle generator                                     *)
(*                                                                       *)
(*************************************************************************)

Theorem source_toggle_code_generator_internal :
  SourceToggleCodeGenerator.
Proof.
  intro e.
  destruct (source_toggle_point_exists e) as [u Hu].
  exists u.
  unfold SourceTogglePointCode.
  rewrite Prov_iff_Thm.
  exact Hu.
Qed.