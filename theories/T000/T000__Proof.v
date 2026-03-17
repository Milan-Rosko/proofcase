(* `T000__Proof.v` *)

From Coq Require Import Arith Bool List PeanoNat.
Import ListNotations.

From T000 Require Import
  R00__Odd_Part
  R01__Pigeonhole_Divisibility.

(*************************************************************************)
(*                                                                       *)
(*   Proofcase / Pigeonhole Divisibility -- Audit Layer                  *)
(*                                                                       *)
(*   This file serves as the proof-theoretic synopsis of `T000`.  It     *)
(*   introduces no new mathematical content.  Rather, it reorganizes     *)
(*   the derivational spine of the template package and re-exports its   *)
(*   principal arithmetic objects, its finite codomain control lemmas,   *)
(*   its abstract combinatorial collision theorem, and its final         *)
(*   divisibility endpoint in one place.                                 *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  Overview
  --------

  `T000` has one main constructive route. It remains the recommended template
  for small, closed Proofcase packages whose proofs factor into a clean sequence
  of explicit local lemmas and one final endpoint theorem.

  (i) Main Result

    (a) Arithmetic normal-form layer.

        Every positive integer is decomposed into a power of two times an odd
        factor.  The odd factor is treated as the canonical invariant relevant
        to divisibility.

    (b) Finite odd-codomain layer.

        For inputs restricted to `{1, ..., 2n}`, the odd-part map lands inside
        the explicit n-element list `odd_range n` of odd values.

    (c) Combinatorial collision layer.

        A generic list-based pigeonhole principle converts the cardinality gap
        `|A| = n + 1` versus `|odd_range n| = n` into a pair of distinct
        elements with equal odd part.

    (d) Endpoint transfer.

        Equality of odd parts is translated back into the divisibility
        conclusion by comparing the respective 2-adic exponents.
*)

(*************************************************************************)
(*                                                                       *)
(*                   ARITHMETIC NORMAL-FORM LAYER                        *)
(*                                                                       *)
(*************************************************************************)

(*
  (a)
  ARITHMETIC NORMAL-FORM LAYER
*)

(*
  (1)
  Auxiliary recursion computing the odd part of a natural number by
  repeatedly removing factors of 2.  The fuel is a structural device
  ensuring totality of the recursive program inside Rocq; mathematically,
  the intended output is the odd factor in the 2-adic decomposition.
*)

Definition audit_odd_part_aux : nat -> nat -> nat :=
  odd_part_aux.

(*
  (2)
  Canonical odd-part normalization map.  This is the arithmetic invariant
  used throughout the package to collapse the ambient interval
  `{1, ..., 2n}` onto only `n` relevant odd classes.
*)

Definition audit_odd_part : nat -> nat :=
  odd_part.

(*
  (3)
  Auxiliary recursion for the 2-adic valuation, i.e. the exponent of the
  highest power of `2` dividing the input.  Together with `odd_part`, this
  records the full decomposition of a positive integer into its dyadic
  exponent and its odd residue.
*)

Definition audit_val2_aux : nat -> nat -> nat :=
  val2_aux.

(*
  (4)
  Canonical 2-adic valuation map.  It measures the dyadic depth of an
  integer and is the companion invariant to `odd_part` in the package's
  normal-form analysis.
*)

Definition audit_val2 : nat -> nat :=
  val2.

(*
  (5)
  Certification that the normalization really lands in the odd stratum:
  every positive integer has an odd odd part.  This is the first half of
  the arithmetic preparation for the finite pigeonhole target.
*)

Definition audit_odd_part_odd :
  forall n,
    1 <= n ->
    Nat.odd (audit_odd_part n) = true :=
  odd_part_odd.

(*
  (6)
  The normalized odd part is not merely associated to the original input;
  it actually divides it.  This identifies `odd_part` as a genuine divisor
  extracted canonically from the number.
*)

Definition audit_odd_part_divides :
  forall n,
    1 <= n ->
    Nat.divide (audit_odd_part n) n :=
  odd_part_divides.

(*
  (7)
  Full decomposition theorem: every positive integer factors as a power
  of `2` multiplied by its odd part.  This is the structural statement that
  later turns equality of odd parts into a direct divisibility relation.
*)

Definition audit_decomposition :
  forall n,
    1 <= n ->
    n = 2 ^ (audit_val2 n) * audit_odd_part n :=
  decomposition.

(*
  (8)
  Arithmetic comparison theorem.  If two positive integers share the same
  odd part, then their difference lies entirely in the 2-adic exponent,
  so one of them must divide the other.
*)

Definition audit_same_odd_part_divides :
  forall a b,
    1 <= a ->
    1 <= b ->
    audit_odd_part a = audit_odd_part b ->
    Nat.divide a b \/ Nat.divide b a :=
  same_odd_part_divides.

(*************************************************************************)
(*                                                                       *)
(*                    FINITE ODD-CODOMAIN LAYER                          *)
(*                                                                       *)
(*************************************************************************)

(*
  (b)
  FINITE ODD-CODOMAIN LAYER
*)

(*
  (1)
  Explicit finite codomain for the odd-part map on `{1, ..., 2n}`: the list
  of the first n positive odd numbers.  This is the concrete carrier of
  the pigeonholes used in the main theorem.
*)

Definition audit_odd_range : nat -> list nat :=
  odd_range.

(*
  (2)
  Cardinality computation for the codomain list.  This is the precise
  quantitative input needed to compare the n odd categories against an
  (n+1)-element source list.
*)

Definition audit_odd_range_length :
  forall n,
    length (audit_odd_range n) = n :=
  odd_range_length.

(*
  (3)
  Structural characterization of the codomain list: membership in
  `odd_range n` is equivalent to being representable as `2i + 1` for some
  index i strictly below n.
*)

Definition audit_odd_range_in_iff :
  forall n k,
    In k (audit_odd_range n) <-> exists i, i < n /\ k = 2 * i + 1 :=
  odd_range_in_iff.

(*
  (4)
  The codomain list is duplicate-free.  This ensures that `odd_range n`
  behaves as a genuine finite family of n distinct categories rather than
  merely as a list with repeated labels.  In particular, the subsequent
  cardinality comparison is mathematically honest at the level of distinct
  values and not just list length.
*)

Definition audit_odd_range_NoDup :
  forall n,
    NoDup (audit_odd_range n) :=
  odd_range_NoDup.

(*
  (5)
  Bridge from arithmetic normalization to finite codomain control:
  whenever `a` lies in `{1, ..., 2n}`, its odd part belongs to `odd_range n`.
  This is the exact input needed to instantiate the abstract pigeonhole
  principle with the odd-part map.
*)

Definition audit_odd_part_in_range :
  forall n a,
    1 <= a ->
    a <= 2 * n ->
    In (audit_odd_part a) (audit_odd_range n) :=
  odd_part_in_range.

(*************************************************************************)
(*                                                                       *)
(*                  COMBINATORIAL COLLISION LAYER                        *)
(*                                                                       *)
(*************************************************************************)

(*
  (c)
  COMBINATORIAL COLLISION LAYER
*)

(*
  (1)
  Generic list-based pigeonhole principle.  It is phrased abstractly so
  that the combinatorial collision mechanism is cleanly separated from
  the number-theoretic content of odd parts and divisibility.  This
  separation is part of the template discipline: the combinatorial engine
  should remain reusable, while arithmetic meaning enters only through the
  choice of the map and the target category list.
*)

Definition audit_pigeonhole :
  forall (A : Type) (f : A -> nat) (xs : list A) (cats : list nat),
    NoDup xs ->
    (forall x, In x xs -> In (f x) cats) ->
    length cats < length xs ->
    exists a b,
      In a xs /\
      In b xs /\
      a <> b /\
      f a = f b :=
  pigeonhole.

(*************************************************************************)
(*                                                                       *)
(*                        ENDPOINT TRANSFER                              *)
(*                                                                       *)
(*************************************************************************)

(*
  (d)
  ENDPOINT TRANSFER
*)

(*
  (1)
  Principal `T000` endpoint.  The abstract collision theorem is applied to
  the odd-part map on a duplicate-free list `A` of length `n + 1` contained in
  `{1, ..., 2n}`; the resulting same-odd-part pair is then discharged by the
  arithmetic comparison theorem to obtain a divisibility pair.
*)

Definition audit_pigeonhole_divisibility :
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
    exists a b,
      In a A /\
      In b A /\
      a <> b /\
      (Nat.divide a b \/ Nat.divide b a) :=
  pigeonhole_divisibility.

(*
  (2)
  Canonical public alias for the package endpoint.  This gives downstream
  readers a stable theorem name inside the audit layer without changing the
  mathematical content.  In audit-facing reading, this is the preferred
  symbol under which the entire `T000` route may be cited.
*)

Definition audit_template_endpoint :
  forall n A,
    (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->
    NoDup A ->
    length A = n + 1 ->
  exists a b,
      In a A /\
      In b A /\
      a <> b /\
      (Nat.divide a b \/ Nat.divide b a) :=
  pigeonhole_divisibility.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Pigeonhole Divisibility                                            *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Normalize each admissible input `a` by passing to          *)
(*            `odd_part a`.                                              *)
(*                                                                       *)
(*    Step 2. Show that all such normalized values lie in `odd_range n`, *)
(*            an explicit n-element family of odd numbers.               *)
(*                                                                       *)
(*    Step 3. Apply the abstract pigeonhole theorem to the `n + 1`       *)
(*            source elements and the `n` target categories to obtain    *)
(*            a collision.                                               *)
(*                                                                       *)
(*    Step 4. Convert that collision back into divisibility using the    *)
(*            decomposition `a = 2^(val2 a) * odd_part a`.               *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    `forall n A,`                                                      *)
(*    `  (forall a, In a A -> 1 <= a /\ a <= 2 * n) ->`                  *)
(*    `  NoDup A ->`                                                     *)
(*    `  length A = n + 1 ->`                                            *)
(*    `  exists a b,`                                                    *)
(*    `    In a A /\ In b A /\ a <> b /\`                                *)
(*    `    (Nat.divide a b \/ Nat.divide b a)`                           *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Any list `A` of `n + 1` pairwise distinct naturals drawn from the  *)
(*    interval `{1, ..., 2n}` contains two distinct elements such that   *)
(*    one divides the other.  The proof proceeds by sending each         *)
(*    element of `A` to its odd part, observing that these images all lie*)
(*    in the explicit n-element odd list `odd_range n`, invoking the     *)
(*    pigeonhole principle to obtain two distinct source elements with   *)
(*    the same odd part, and finally comparing their 2-adic valuations   *)
(*    to conclude divisibility in one direction or the other.  In this   *)
(*    sense, the theorem is an interplay between a finite counting       *)
(*    argument and a canonical arithmetic normal form.                   *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This theorem is closed in the ambient context and carries no       *)
(*    non-constructive assumptions.  It is therefore not merely the      *)
(*    final claim of `T000` but also the model example of the Proofcase  *)
(*    design principle that a package should expose its conceptual       *)
(*    route explicitly: arithmetic normalization, finite codomain        *)
(*    control, abstract combinatorics, and terminal discharge.  The      *)
(*    present file is intended to make that route legible to a reader    *)
(*    who wants the proof architecture before descending into the        *)
(*    implementation details of the source lemmas.                       *)
(*                                                                       *)
(*************************************************************************)

End Proof_Index.

Print Assumptions same_odd_part_divides.
Print Assumptions pigeonhole.
Print Assumptions pigeonhole_divisibility.
