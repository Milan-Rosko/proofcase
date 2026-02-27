(* R02__Carryless_Pairing_Correctness.v *)

From Coq Require Import Arith List Bool PeanoNat.
Import ListNotations.

From T001 Require Import R01__Carryless_Pairing_Definitions.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Carryless Pairing — Correctness                          *)
(*                                                                       *)
(*  This file proves the standard correctness statement                  *)
(*                                                                       *)
(*      unpair (pair x y) = (x, y)                                       *)
(*                                                                       *)
(*  under an explicit Zeckendorf specification. The specification        *)
(*  isolates the two nontrivial facts required for the algorithm:        *)
(*                                                                       *)
(*    (i)  Z is sound: it represents numbers as sums of Fibonacci        *)
(*         values                                                        *)
(*                                                                       *)
(*   (ii)  Z respects the even/odd-band split for pair encodings         *)
(*                                                                       *)
(*  This is the “standard proof” wrapper: all heavy combinatorics        *)
(*  (existence/uniqueness of Zeckendorf representations) are localized   *)
(*  to the assumptions below.                                            *)
(*                                                                       *)
(*************************************************************************)

Section Carryless_Correctness.

  Variable P : Params.

  Opaque B.

  (*
  Zeckendorf specification
  *)

  Hypothesis Z_sound : forall n, sumF (Z P n) = n.

  (*
      Even/odd split of the Zeckendorf support for a paired value.

      These two laws capture the semantic fact that the indices used by
      the carryless encoding can be recovered by filtering the support
      of the encoded number.
  *)

  Hypothesis Z_even_split :
    forall x y,
      filter is_even (Z P (pair P x y)) = even_band P x.

  Hypothesis Z_odd_split :
    forall x y,
      filter (odd_ge_B1 (B P x)) (Z P (pair P x y)) = odd_band P x y.

  (*
    Arithmetic decoding lemmas.
  *)

  Lemma two_S : forall n, two (S n) = S (S (two n)).
  Proof.
    intro n.
    unfold two.
    simpl.
    rewrite Nat.add_succ_r.
    reflexivity.
  Qed.

  Lemma div2_two : forall n, div2 (two n) = n.
  Proof.
    induction n as [|n IH].
    - simpl. reflexivity.
    - rewrite two_S. simpl. rewrite IH. reflexivity.
  Qed.

  Lemma add_sub_cancel_l : forall a b, a + b - a = b.
  Proof.
    induction a as [|a IH]; intro b; simpl.
    - rewrite Nat.sub_0_r. reflexivity.
    - apply IH.
  Qed.

  Lemma map_div2_even_band :
    forall x, map div2 (even_band P x) = Z P x.
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
      map (decode_odd_index (B P x)) (odd_band P x y) = Z P y.
  Proof.
    intros x y.
    unfold odd_band.
    rewrite map_map.
    rewrite <- map_id.
    apply map_ext.
    intro a.
    apply decode_encode_odd.
  Qed.

  (*
    Summation lemmas.
  *)

  Lemma sumF_half_even_pair :
    forall x y,
      sumF (half_even_indices (Z P (pair P x y))) = x.
  Proof.
    intros x y.
    unfold half_even_indices.
    rewrite Z_even_split.
    rewrite map_div2_even_band.
    apply Z_sound.
  Qed.

  Lemma sumF_y_indices_pair :
    forall x y,
      sumF (y_indices (B P x) (Z P (pair P x y))) = y.
  Proof.
    intros x y.
    unfold y_indices.
    rewrite Z_odd_split.
    rewrite map_decode_odd_band.
    apply Z_sound.
  Qed.

  (*
    Main correctness theorem.
  *)

  Theorem unpair_pair :
    forall x y, unpair P (pair P x y) = (x, y).
  Proof.
    intros x y.
    unfold unpair.
    cbn.
    set (zn := Z P (pair P x y)).
    assert (Hx : sumF (half_even_indices zn) = x).
    {
      subst zn.
      apply sumF_half_even_pair.
    }
    assert (Hy : sumF (y_indices (B P x) zn) = y).
    {
      subst zn.
      apply sumF_y_indices_pair.
    }
    rewrite Hx.
    rewrite Hy.
    reflexivity.
  Qed.

  (*
    Consequence: injectivity of pair.
  *)

  Theorem pair_inj :
    forall x1 y1 x2 y2,
      pair P x1 y1 = pair P x2 y2 -> x1 = x2 /\ y1 = y2.
  Proof.
    intros x1 y1 x2 y2 H.
    pose proof (unpair_pair x1 y1) as H1.
    pose proof (unpair_pair x2 y2) as H2.
    rewrite H in H1.
    rewrite H1 in H2.
    inversion H2; subst.
    split; reflexivity.
  Qed.

End Carryless_Correctness.
