(* R01__Pigeonhole_Divisibility.v *)

From Coq Require Import Arith Bool Lia List PeanoNat.
Import ListNotations.

From T000 Require Import R01__Odd_Part.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Pigeonhole Divisibility — Main Theorem                   *)
(*                                                                       *)
(*  We prove that any subset A of {1, ..., 2n} with |A| = n+1 contains   *)
(*  two distinct elements a, b such that a | b or b | a.                 *)
(*                                                                       *)
(*  The proof proceeds in three steps:                                   *)
(*                                                                       *)
(*    (i)   We state a list-based pigeonhole principle: if a map sends   *)
(*          n+1 distinct values into a codomain of size n, two inputs    *)
(*          collide.                                                     *)
(*                                                                       *)
(*    (ii)  We apply it to the odd-part map on the elements of A, whose  *)
(*          codomain is the n odd numbers in {1, ..., 2n}.               *)
(*                                                                       *)
(*    (iii) We invoke same_odd_part_divides from R01 to conclude.        *)
(*                                                                       *)
(*************************************************************************)

Section Pigeonhole.

(*
  A list-based pigeonhole principle.  If we map a NoDup list of length
  n+1 into a list of n categories, two distinct elements of the source
  must map to the same category.
*)

Theorem pigeonhole :
  forall (A : Type) (f : A -> nat) (xs : list A) (cats : list nat),
    NoDup xs ->
    (forall x, In x xs -> In (f x) cats) ->
    length cats < length xs ->
    exists a b,
      In a xs /\
      In b xs /\
      a <> b /\
      f a = f b.
Proof.
  intros A f xs.
  induction xs as [|x xs IH]; intros cats Hnodup Hcat Hlen.
  - simpl in Hlen. lia.
  - apply NoDup_cons_iff in Hnodup.
    destruct Hnodup as [Hnotin_x Hnodup_xs].
    destruct (in_dec Nat.eq_dec (f x) (map f xs)) as [Hin | Hnotin].
    + apply in_map_iff in Hin.
      destruct Hin as [y [Hy_eq Hy_in]].
      exists x, y.
      repeat split.
      * simpl. left. reflexivity.
      * simpl. right. exact Hy_in.
      * intro Hxy. subst y. contradiction.
      * symmetry. exact Hy_eq.
    + assert (Hcat_xs :
          forall y, In y xs -> In (f y) (remove Nat.eq_dec (f x) cats)).
      { intros y Hy.
        specialize (Hcat y (or_intror Hy)) as Hy_cat.
        assert (Hy_map : In (f y) (map f xs)).
        { apply in_map. exact Hy. }
        assert (Hneq_fx : f y <> f x).
        { intro Heq.
          rewrite Heq in Hy_map.
          contradiction. }
        eapply in_in_remove.
        - exact Hneq_fx.
        - exact Hy_cat. }
      assert (Hlen_xs : length (remove Nat.eq_dec (f x) cats) < length xs).
      { specialize (Hcat x (or_introl eq_refl)) as Hfx_cat.
        pose proof (remove_length_lt Nat.eq_dec cats (f x) Hfx_cat) as Hrm.
        simpl in Hlen.
        lia. }
      specialize (IH (remove Nat.eq_dec (f x) cats) Hnodup_xs Hcat_xs Hlen_xs).
      destruct IH as [a [b [Ha [Hb [Hab Hf]]]]].
      exists a, b.
      repeat split.
      * simpl. right. exact Ha.
      * simpl. right. exact Hb.
      * exact Hab.
      * exact Hf.
Qed.

End Pigeonhole.

Section Main_Theorem.

(*
  We represent the subset A as a list of distinct naturals drawn from
  {1, ..., 2n}.  The hypotheses are:

    - elements_bound:  every element of A is between 1 and 2n
    - elements_NoDup:  the elements of A are pairwise distinct
    - elements_size:   |A| = n + 1
*)

Variable n : nat.
Variable A : list nat.

Hypothesis elements_bound :
  forall a, In a A -> 1 <= a /\ a <= 2 * n.

Hypothesis elements_NoDup :
  NoDup A.

Hypothesis elements_size :
  length A = n + 1.

(*
  Main theorem: A contains two distinct elements where one divides
  the other.
*)

Theorem pigeonhole_divisibility :
  exists a b,
    In a A /\
    In b A /\
    a <> b /\
    (Nat.divide a b \/ Nat.divide b a).
Proof.

  (*
    Step 1.  We apply the pigeonhole principle with the odd-part map
    and the list odd_range n as the set of categories.
  *)
  
  destruct (pigeonhole nat odd_part A (odd_range n)) as [a [b [Ha [Hb [Hneq Heq]]]]].
  - exact elements_NoDup.
  - intros x Hx.
    destruct (elements_bound x Hx) as [Hlo Hhi].
    apply odd_part_in_range.
    + exact Hlo.
    + exact Hhi.
  - rewrite odd_range_length.
    rewrite elements_size.
    lia.

  (*
    Step 2.  We have a <> b in A with odd_part a = odd_part b.
    By same_odd_part_divides, one divides the other.
  *)
  
  - exists a, b.
    repeat split.
    + exact Ha.
    + exact Hb.
    + exact Hneq.
    + apply same_odd_part_divides.
      * destruct (elements_bound a Ha). exact H.
      * destruct (elements_bound b Hb). exact H.
      * exact Heq.
Qed.

(*
  The bound n + 1 is tight: the set {n+1, n+2, ..., 2n} has exactly n
  elements and contains no pair where one divides the other (for n >= 2).
  We record this as a remark rather than a formal proof.
*)

End Main_Theorem.
