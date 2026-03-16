(* R02__Local_Lemmas.v *)

From Coq Require Import Arith Bool Lia List ZArith.
Import ListNotations.

From T004 Require Import
  R00__Base
  R01__Seed.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 1 — Local Lemmas                           *)
(*                                                                       *)
(*  Center-window extraction and small locality lemmas for the canonical *)
(*  single-seed trajectory.                                              *)
(*                                                                       *)
(*************************************************************************)

Section Local_Lemmas.

(*
  Integer segment [start, start + len - 1].
*)

Fixpoint z_segment (start : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => []
  | S len' => start :: z_segment (start + 1) len'
  end.

(*
  Coordinates from -n to n.
*)

Definition centered_coords (n : nat) : list Z :=
  z_segment (- Z.of_nat n) (S (2 * n)).

(*
  Width-(2n+1) centered window cut from the canonical row at time t.
*)

Definition center_window (n t : nat) : list bit :=
  map (canonical_row t) (centered_coords n).

(*
  The center bit is the width-0 centered window.
*)

Definition center_strip (t : nat) : bit :=
  canonical_row t 0%Z.

Lemma centered_coords_width0 :
  centered_coords 0%nat = [0%Z].
Proof.
  reflexivity.
Qed.

Lemma center_window_width0 :
  forall t,
    center_window 0%nat t = [center_strip t].
Proof.
  intro t.
  unfold center_window, center_strip.
  rewrite centered_coords_width0.
  reflexivity.
Qed.

(*
  One-step update at the center.
*)

Lemma center_update :
  forall t,
    center_strip (S t) =
      rule30
        (canonical_row t (-1)%Z)
        (canonical_row t 0%Z)
        (canonical_row t 1%Z).
Proof.
  intro t.
  unfold center_strip.
  rewrite canonical_row_step.
  unfold step.
  reflexivity.
Qed.

(*
  Canonical rows depend only on the backward light cone.
*)

Lemma canonical_row_depends_on_interval :
  forall t r,
    same_on_interval r seed_row 0%Z t ->
    iter_row t r 0%Z = center_strip t.
Proof.
  intros t r Hagree.
  unfold center_strip, canonical_row.
  apply iter_row_locality.
  exact Hagree.
Qed.

(*
  The seed starts active at the center.
*)

Lemma center_strip_zero :
  center_strip 0%nat = true.
Proof.
  unfold center_strip.
  rewrite canonical_row_zero.
  exact seed_row_at_zero.
Qed.

Lemma center_window_zero :
  forall n,
    center_window n 0%nat = map seed_row (centered_coords n).
Proof.
  intro n.
  unfold center_window.
  rewrite canonical_row_zero.
  reflexivity.
Qed.

End Local_Lemmas.
