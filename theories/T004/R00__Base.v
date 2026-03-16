(* R00__Base.v *)

From Coq Require Import Arith Bool Lia List PeanoNat ZArith.
Import ListNotations.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Finite Obstruction — Base Dynamics               *)
(*                                                                       *)
(*  Core Rule-30 semantics on bi-infinite rows and discrete spacetime.   *)
(*  We define the local update rule, global step, iteration, interval    *)
(*  agreement, spatial shifts, and prove locality and shift transport.   *)
(*                                                                       *)
(*************************************************************************)

Section Base_Definitions.

(*
  Binary state of one Rule 30 cell.
*)

Definition bit := bool.
Definition cell := bit.

(*
  Bi-infinite row indexed by Z.
*)

Definition row := Z -> cell.

(*
  Discrete spacetime indexed by time then space.
*)

Definition space_time := nat -> row.

(*
  Rule 30 local update.
*)

Definition rule30 (a b c : cell) : cell :=
  xorb a (orb b c).

(*
  One global Rule 30 update on rows.
*)

Definition step_row (r : row) : row :=
  fun x => rule30 (r (x - 1)) (r x) (r (x + 1)).

Definition step : row -> row :=
  step_row.

(*
  Iteration of the global Rule 30 update.
*)

Fixpoint iter_row (n : nat) (r : row) : row :=
  match n with
  | 0%nat => r
  | S n' => step_row (iter_row n' r)
  end.

(*
  Membership in the radius-n interval around x.
*)

Definition in_interval (x : Z) (n : nat) (y : Z) : Prop :=
  x - Z.of_nat n <= y <= x + Z.of_nat n.

(*
  Agreement of two rows on the interval [x-n, x+n].
*)

Definition same_on_interval (u v : row) (x : Z) (n : nat) : Prop :=
  forall y, in_interval x n y -> u y = v y.

(*
  Spatial shift of a row by offset k.
*)

Definition shift_row (k : Z) (r : row) : row :=
  fun x => r (x - k).

(*
  One-step evolution law.
*)

Definition evolves (u : space_time) : Prop :=
  forall t x,
    u (S t) x = rule30 (u t (x - 1)) (u t x) (u t (x + 1)).

End Base_Definitions.

Section Base_Properties.

(*
  Exhaustive truth table for Rule 30.
*)

Theorem rule30_truth_table :
  forall a b c,
    rule30 a b c =
      match a, b, c with
      | false, false, false => false
      | false, false, true => true
      | false, true, false => true
      | false, true, true => true
      | true, false, false => true
      | true, false, true => false
      | true, true, false => false
      | true, true, true => false
      end.
Proof.
  intros a b c.
  destruct a, b, c; reflexivity.
Qed.

(*
  Interval agreement can be restricted to any smaller radius.
*)

Lemma same_on_interval_weaken :
  forall u v x n m,
    (m <= n)%nat ->
    same_on_interval u v x n ->
    same_on_interval u v x m.
Proof.
  intros u v x n m Hmn Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  assert (Hmn_z : (Z.of_nat m <= Z.of_nat n)%Z).
  { apply Nat2Z.inj_le. exact Hmn. }
  lia.
Qed.

(*
  Radius (S n) agreement implies radius n agreement at the same center.
*)

Lemma same_on_interval_shift_center :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v x n.
Proof.
  intros u v x n Hsame.
  eapply same_on_interval_weaken.
  - apply Nat.le_succ_diag_r.
  - exact Hsame.
Qed.

(*
  Radius (S n) agreement around x implies radius n agreement around x-1.
*)

Lemma same_on_interval_shift_left :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v (x - 1) n.
Proof.
  intros u v x n Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(*
  Radius (S n) agreement around x implies radius n agreement around x+1.
*)

Lemma same_on_interval_shift_right :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval u v (x + 1) n.
Proof.
  intros u v x n Hsame y Hy.
  apply Hsame.
  unfold in_interval in *.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.

(*
  One Rule 30 step shrinks the required agreement radius by one.
*)

Lemma step_row_locality :
  forall u v x n,
    same_on_interval u v x (S n) ->
    same_on_interval (step_row u) (step_row v) x n.
Proof.
  intros u v x n Hsame y Hy.
  unfold step_row.
  assert (Hleft : u (y - 1) = v (y - 1)).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  assert (Hmid : u y = v y).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  assert (Hright : u (y + 1) = v (y + 1)).
  { apply Hsame.
    unfold in_interval in *.
    rewrite Nat2Z.inj_succ.
    lia. }
  rewrite Hleft, Hmid, Hright.
  reflexivity.
Qed.

(*
  Finite-speed dependence: after n steps, position x depends only on
  initial values in [x-n, x+n].
*)

Theorem iter_row_locality :
  forall n x u v,
    same_on_interval u v x n ->
    iter_row n u x = iter_row n v x.
Proof.
  induction n as [|n IH]; intros x u v Hsame.
  - simpl.
    apply Hsame.
    unfold in_interval.
    simpl.
    lia.
  - simpl.
    assert (Hleft : iter_row n u (x - 1) = iter_row n v (x - 1)).
    { apply IH.
      apply same_on_interval_shift_left.
      exact Hsame. }
    assert (Hmid : iter_row n u x = iter_row n v x).
    { apply IH.
      apply same_on_interval_shift_center.
      exact Hsame. }
    assert (Hright : iter_row n u (x + 1) = iter_row n v (x + 1)).
    { apply IH.
      apply same_on_interval_shift_right.
      exact Hsame. }
    unfold step_row.
    rewrite Hleft, Hmid, Hright.
    reflexivity.
Qed.

(*
  One-step update commutes with spatial shifts, pointwise.
*)

Lemma step_row_shift_value :
  forall r k x,
    step_row (shift_row k r) x = shift_row k (step_row r) x.
Proof.
  intros r k x.
  unfold step_row, shift_row.
  replace ((x - 1) - k) with ((x - k) - 1) by lia.
  replace ((x + 1) - k) with ((x - k) + 1) by lia.
  reflexivity.
Qed.

(*
  Iterated updates commute with spatial shifts, pointwise.
*)

Lemma iter_row_shift_value :
  forall n r k x,
    iter_row n (shift_row k r) x = shift_row k (iter_row n r) x.
Proof.
  induction n as [|n IH]; intros r k x.
  - simpl. reflexivity.
  - simpl.
    unfold step_row.
    rewrite (IH r k (x - 1)).
    rewrite (IH r k x).
    rewrite (IH r k (x + 1)).
    unfold shift_row.
    replace ((x - 1) - k) with ((x - k) - 1) by lia.
    replace ((x + 1) - k) with ((x - k) + 1) by lia.
    reflexivity.
Qed.

End Base_Properties.
