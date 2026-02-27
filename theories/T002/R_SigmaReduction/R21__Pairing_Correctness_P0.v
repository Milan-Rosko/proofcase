(* R21__Pairing_Correctness_P0.v *)

From Coq Require Import Arith List Lia.
Import ListNotations.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf.

Lemma div2_two : forall n, div2 (two n) = n.
Proof.
  induction n as [|n IH].
  - simpl. reflexivity.
  - rewrite two_S. simpl. rewrite IH. reflexivity.
Qed.

Lemma add_sub_cancel_l : forall a b, a + b - a = b.
Proof.
  intros a b. lia.
Qed.

Lemma map_div2_even_band :
  forall x, map div2 (even_band P0 x) = Z0 x.
Proof.
  intro x.
  unfold even_band.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  apply div2_two.
Qed.

Lemma decode_encode_odd :
  forall Bx j,
    decode_odd_index Bx (Bx + two_j_minus1 j) = j.
Proof.
  intros Bx j.
  unfold decode_odd_index, two_j_minus1.
  rewrite (add_sub_cancel_l Bx (Nat.pred (two j))).
  destruct j as [|j'].
  - simpl. reflexivity.
  - rewrite two_S. simpl. rewrite div2_two. reflexivity.
Qed.

Lemma map_decode_odd_band :
  forall x y,
    map (decode_odd_index (B P0 x)) (odd_band P0 x y) = Z0 y.
Proof.
  intros x y.
  unfold odd_band.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext.
  intro a.
  apply decode_encode_odd.
Qed.

Theorem unpair_pair_P0 :
  forall x y, unpair P0 (pair P0 x y) = (x, y).
Proof.
  intros x y.
  unfold unpair.
  set (zn := Z0 (pair P0 x y)).
  set (x0 := sumF (half_even_indices zn)).
  set (Bx := B P0 x0).
  set (y0 := sumF (y_indices Bx zn)).
  change ((x0, y0) = (x, y)).
  assert (Hx : x0 = x).
  {
    subst x0 zn.
    unfold half_even_indices.
    rewrite Z0_even_split.
    rewrite map_div2_even_band.
    apply Z0_sound.
  }
  assert (Hy : y0 = y).
  {
    subst y0 Bx zn.
    rewrite Hx.
    unfold y_indices.
    rewrite Z0_odd_split.
    rewrite map_decode_odd_band.
    apply Z0_sound.
  }
  now rewrite Hx, Hy.
Qed.
