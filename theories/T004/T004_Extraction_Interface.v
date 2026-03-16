(* T004_Extraction_Interface.v *)

From Coq Require Import Extraction List ZArith.
Import ListNotations.

From T004 Require Import
  R00__Base
  R01__Seed
  R02__Local_Lemmas
  R03__Periodicity
  R04__Center_No_Pure_Periodicity
  R05__Glitch_Compactness
  R06__Mixed_Periodicity
  R07__Classic_Semantics.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 1 -- OCaml extraction interface            *)
(*                                                                       *)
(*  Theorems erase under extraction, so this file exposes the concrete   *)
(*  computational surface of T004: finite centered windows, seeded       *)
(*  prefixes, truncations, and small numeric views that are practical    *)
(*  to inspect from OCaml.                                               *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
  (1)
  We encode a bit as a natural number for OCaml inspection.
*)

Definition bit_to_nat (b : bit) : nat :=
  if b then 1%nat else 0%nat.

(*
  (2)
  We encode a finite bit list as a natural-number list.
*)

Definition bit_list_to_nat_list (xs : list bit) : list nat :=
  map bit_to_nat xs.

(*
  (3)
  We extract the centered finite window of an arbitrary row.
*)

Definition row_window (r : row) (radius : nat) : list bit :=
  map r (centered_coords radius).

(*
  (4)
  We expose that centered row window in nat-coded form.
*)

Definition row_window_as_nat (r : row) (radius : nat) : list nat :=
  bit_list_to_nat_list (row_window r radius).

(*
  (5)
  We expose the canonical seed window.
*)

Definition seed_window (radius : nat) : list bit :=
  row_window seed_row radius.

(*
  (6)
  We expose the canonical seed window in nat-coded form.
*)

Definition seed_window_as_nat (radius : nat) : list nat :=
  row_window_as_nat seed_row radius.

(*
  (7)
  We expose a single canonical cell value.
*)

Definition canonical_value (t : nat) (x : Z) : bit :=
  canonical_row t x.

(*
  (8)
  We expose a single canonical cell value in nat-coded form.
*)

Definition canonical_value_as_nat (t : nat) (x : Z) : nat :=
  bit_to_nat (canonical_value t x).

(*
  (9)
  We expose a finite window cut from an arbitrary spacetime trajectory.
*)

Definition trajectory_window (u : space_time) (radius t : nat) : list bit :=
  window_data u radius t.

(*
  (10)
  We expose a trajectory window in nat-coded form.
*)

Definition trajectory_window_as_nat
    (u : space_time) (radius t : nat) : list nat :=
  bit_list_to_nat_list (trajectory_window u radius t).

(*
  (11)
  We expose a finite list of consecutive trajectory windows.
*)

Fixpoint trajectory_windows_from
    (u : space_time) (radius start len : nat) : list (list bit) :=
  match len with
  | 0%nat => []
  | S len' =>
      trajectory_window u radius start ::
      trajectory_windows_from u radius (S start) len'
  end.

(*
  (12)
  We expose the finite prefix of trajectory windows from time 0.
*)

Definition trajectory_prefix_windows
    (u : space_time) (radius height : nat) : list (list bit) :=
  trajectory_windows_from u radius 0%nat (S height).

(*
  (13)
  We expose the same trajectory prefix in nat-coded form.
*)

Definition trajectory_prefix_windows_as_nat
    (u : space_time) (radius height : nat) : list (list nat) :=
  map bit_list_to_nat_list (trajectory_prefix_windows u radius height).

(*
  (14)
  We expose the canonical centered window at time t.
*)

Definition canonical_window (radius t : nat) : list bit :=
  center_window radius t.

(*
  (15)
  We expose the canonical centered window in nat-coded form.
*)

Definition canonical_window_as_nat (radius t : nat) : list nat :=
  bit_list_to_nat_list (canonical_window radius t).

(*
  (16)
  We expose a finite canonical prefix of centered windows.
*)

Definition canonical_prefix_windows
    (radius height : nat) : list (list bit) :=
  trajectory_prefix_windows canonical_row radius height.

(*
  (17)
  We expose the same canonical prefix in nat-coded form.
*)

Definition canonical_prefix_windows_as_nat
    (radius height : nat) : list (list nat) :=
  trajectory_prefix_windows_as_nat canonical_row radius height.

(*
  (18)
  We expose windows from the canonically shifted trajectory.
*)

Definition shifted_canonical_window
    (period radius t : nat) : list bit :=
  trajectory_window (shifted_canonical_trajectory period) radius t.

(*
  (19)
  We expose shifted canonical windows in nat-coded form.
*)

Definition shifted_canonical_window_as_nat
    (period radius t : nat) : list nat :=
  bit_list_to_nat_list (shifted_canonical_window period radius t).

(*
  (20)
  We expose finite prefixes from the shifted canonical trajectory.
*)

Definition shifted_canonical_prefix_windows
    (period radius height : nat) : list (list bit) :=
  trajectory_prefix_windows (shifted_canonical_trajectory period) radius height.

(*
  (21)
  We expose those shifted prefixes in nat-coded form.
*)

Definition shifted_canonical_prefix_windows_as_nat
    (period radius height : nat) : list (list nat) :=
  trajectory_prefix_windows_as_nat
    (shifted_canonical_trajectory period) radius height.

(*
  (22)
  We expose the local seed-window model on a finite inspection radius.
*)

Definition local_seed_window_model_window
    (seed_radius window_radius : nat) : list bit :=
  row_window (local_seed_window_model seed_radius) window_radius.

(*
  (23)
  We expose the local seed-window model in nat-coded form.
*)

Definition local_seed_window_model_window_as_nat
    (seed_radius window_radius : nat) : list nat :=
  bit_list_to_nat_list
    (local_seed_window_model_window seed_radius window_radius).

(*
  (24)
  We expose a truncated canonical row on a finite inspection radius.
*)

Definition truncated_canonical_window
    (truncate_radius t window_radius : nat) : list bit :=
  row_window (truncate truncate_radius (canonical_row t)) window_radius.

(*
  (25)
  We expose the truncated canonical row in nat-coded form.
*)

Definition truncated_canonical_window_as_nat
    (truncate_radius t window_radius : nat) : list nat :=
  bit_list_to_nat_list
    (truncated_canonical_window truncate_radius t window_radius).

(*
  (26)
  We expose the finite replay radius used in the compactness route.
*)

Definition extracted_finite_replay_radius (n horizon : nat) : nat :=
  finite_replay_radius n horizon.

End Extraction_Interface.

Extraction Language OCaml.
Set Extraction Output Directory "/Users/wuksh/Codex/Rul30/Proofcase/T004extraction".

Extraction "Original_Sin.ml"
  rule30
  step_row
  iter_row
  centered_coords
  bit_to_nat
  bit_list_to_nat_list
  seed_row
  seed_window
  seed_window_as_nat
  canonical_value
  canonical_value_as_nat
  canonical_row
  canonical_window
  canonical_window_as_nat
  canonical_prefix_windows
  canonical_prefix_windows_as_nat
  shifted_canonical_trajectory
  shifted_canonical_window
  shifted_canonical_window_as_nat
  shifted_canonical_prefix_windows
  shifted_canonical_prefix_windows_as_nat
  local_seed_window_model
  local_seed_window_model_window
  local_seed_window_model_window_as_nat
  truncate
  truncated_canonical_window
  truncated_canonical_window_as_nat
  extracted_finite_replay_radius.

(*************************************************************************)
(*                                                                       *)
(*  KEY ASSUMPTION REPORT                                                *)
(*                                                                       *)
(*  The extraction surface above is computational.  The commands below   *)
(*  expose only the main theorem endpoints and the remaining explicit    *)
(*  open assumptions, so the build output stays readable.                *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*  PHASE 1 ENDPOINT                                                     *)
(*                                                                       *)
(*  Compactness-conditional Phase 1 corollary                            *)
(*                                                                       *)
(*    replay_compactness_principle ->                                    *)
(*      forall n, ~ purely_periodic_center_window n                      *)
(*                                                                       *)
(*  This is part of the package, but it is not the preferred             *)
(*  semantic interface when discussing faithful realizers.               *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions original_sin.
Print Assumptions no_pure_periodicity_of_centered_windows.
Print Assumptions center_strip_not_purely_periodic.

(*************************************************************************)
(*                                                                       *)
(*  PHASE 2 ENDPOINT                                                     *)
(*                                                                       *)
(*  Constructive cutoff-memory theorem                                   *)
(*                                                                       *)
(*    every_cutoff_still_remembers_seed                                  *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions every_cutoff_still_remembers_seed.

(*************************************************************************)
(*                                                                       *)
(*  PHASE 3 STRONG SEMANTIC ENDPOINT                                     *)
(*                                                                       *)
(*  No faithful uniform periodic tail exists.                            *)
(*                                                                       *)
(*  This is the preferred semantic endpoint for the package.             *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions uniformly_eventually_periodic_from_impossible.
Print Assumptions realizable_observational_periodic_tail_from_impossible.
Print Assumptions realizable_uniform_periodic_tail_from_impossible.

(*************************************************************************)
(*                                                                       *)
(*  R07 EXTERNAL CLASSICAL COROLLARY                                     *)
(*                                                                       *)
(*  Under the external semantic-faithfulness premise, eventual           *)
(*  periodicity of centered windows is excluded.  This is the cleanest   *)
(*  assumption-isolating wrapper exported by the package.                *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions classical_semantics_excludes_eventual_periodic_windows.
Print Assumptions classical_semantics_excludes_any_eventual_periodic_window.

(*************************************************************************)
(*                                                                       *)
(*  EXTERNAL PREMISES                                                    *)
(*                                                                       *)
(*  The non-closed ingredients appear as explicit theorem                *)
(*  premises rather than hidden global axioms on the live package        *)
(*  surface.                                                             *)
(*                                                                       *)
(*************************************************************************)
