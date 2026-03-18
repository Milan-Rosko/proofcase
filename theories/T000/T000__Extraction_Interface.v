(* T000__Extraction_Interface.v *)

From Coq Require Import Arith Bool Extraction List PeanoNat.
Import ListNotations.

From T000 Require Import
  R01__Odd_Part
  R02__Pigeonhole_Divisibility.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Pigeonhole Divisibility -- OCaml Extraction Interface    *)
(*                                                                       *)
(*  T000 is primarily a proof package, but its local arithmetic is       *)
(*  executable.  This file exposes a small computational surface for     *)
(*  odd-part analysis, odd-range inspection, and finite witness search   *)
(*  mirroring the main theorem statement.                                *)
(*                                                                       *)
(*************************************************************************)

Section Extraction_Interface.

(*
  (1)
  Executable odd-part data: valuation together with odd part.
*)

Definition odd_part_data (n : nat) : nat * nat :=
  (val2 n, odd_part n).

(*
  (2)
  Bulk odd-part profile for a finite list.
*)

Definition odd_part_profile (xs : list nat) : list (nat * nat) :=
  map odd_part_data xs.

(*
  (3)
  Executable odd-range surface.
*)

Definition odd_range_as_nat_list (n : nat) : list nat :=
  odd_range n.

(*
  (4)
  Boolean membership in a nat list.
*)

Fixpoint member_natb (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => orb (Nat.eqb x y) (member_natb x ys)
  end.

(*
  (5)
  Pointwise image of a list under odd_part.
*)

Definition odd_part_image (xs : list nat) : list nat :=
  map odd_part xs.

(*
  (6)
  Check that every entry of one list belongs to a fixed category list.
*)

Fixpoint all_members_ofb (cats xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (member_natb x cats) (all_members_ofb cats xs')
  end.

(*
  (7)
  Boolean view of "the odd parts land in odd_range n".
*)

Definition all_odd_parts_in_rangeb (n : nat) (xs : list nat) : bool :=
  all_members_ofb (odd_range_as_nat_list n) (odd_part_image xs).

(*
  (8)
  Boolean equality of odd parts.
*)

Definition same_odd_partb (a b : nat) : bool :=
  Nat.eqb (odd_part a) (odd_part b).

(*
  (9)
  Boolean divisibility test, false on zero divisors.
*)

Definition dividesb (a b : nat) : bool :=
  match a with
  | 0 => false
  | S _ => Nat.eqb (Nat.modulo b a) 0
  end.

(*
  (10)
  Boolean bounds check for the interval {1, ..., 2n}.
*)

Definition bounded_by_2n (n a : nat) : bool :=
  andb (Nat.leb 1 a) (Nat.leb a (2 * n)).

(*
  (11)
  Every entry lies in the intended interval.
*)

Fixpoint all_elements_boundedb (n : nat) (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (bounded_by_2n n x) (all_elements_boundedb n xs')
  end.

(*
  (12)
  Boolean distinctness check on a nat list.
*)

Fixpoint all_distinctb (xs : list nat) : bool :=
  match xs with
  | [] => true
  | x :: xs' => andb (negb (member_natb x xs')) (all_distinctb xs')
  end.

(*
  (13)
  Finite boolean packaging of the T000 input hypotheses.
*)

Definition valid_pigeonhole_instanceb (n : nat) (xs : list nat) : bool :=
  andb
    (all_elements_boundedb n xs)
    (andb
      (all_distinctb xs)
      (Nat.eqb (length xs) (S n))).

(*
  (14)
  Search the tail of a list for a partner with the same odd part.
*)

Fixpoint find_same_odd_part_partner
    (a : nat) (xs : list nat) : option nat :=
  match xs with
  | [] => None
  | b :: xs' =>
      if same_odd_partb a b
      then Some b
      else find_same_odd_part_partner a xs'
  end.

(*
  (15)
  Search the whole list for the first same-odd-part collision.
*)

Fixpoint find_same_odd_part_pair
    (xs : list nat) : option (nat * nat) :=
  match xs with
  | [] => None
  | a :: xs' =>
      match find_same_odd_part_partner a xs' with
      | Some b => Some (a, b)
      | None => find_same_odd_part_pair xs'
      end
  end.

(*
  (16)
  Direction of divisibility for a discovered witness pair.
*)

Inductive DivisibilityDirection : Type :=
| Pdw_left_divides_right
| Pdw_right_divides_left.

(*
  (17)
  Finite search result for the extracted witness finder.
*)

Inductive PigeonholeDivisibilityWitnessResult : Type :=
| Pdwr_invalid_input
| Pdwr_no_collision_found
| Pdwr_collision_without_divisibility :
    nat -> nat -> nat -> PigeonholeDivisibilityWitnessResult
| Pdwr_witness :
    nat -> nat -> nat -> DivisibilityDirection ->
    PigeonholeDivisibilityWitnessResult.

(*
  (18)
  Determine which divisibility direction holds for a pair.
*)

Definition classify_divisibility_direction
    (a b : nat) : option DivisibilityDirection :=
  if dividesb a b
  then Some Pdw_left_divides_right
  else
    if dividesb b a
    then Some Pdw_right_divides_left
    else None.

(*
  (19)
  Package a collision as an explicit witness object.
*)

Definition build_witness_from_collision
    (a b : nat) : PigeonholeDivisibilityWitnessResult :=
  let shared_odd_part := odd_part a in
  match classify_divisibility_direction a b with
  | Some direction =>
      Pdwr_witness a b shared_odd_part direction
  | None =>
      Pdwr_collision_without_divisibility a b shared_odd_part
  end.

(*
  (20)
  Best-practice finite witness search mirroring the theorem statement.
*)

Definition search_pigeonhole_divisibility_witness
    (n : nat) (xs : list nat) : PigeonholeDivisibilityWitnessResult :=
  if valid_pigeonhole_instanceb n xs
  then
    match find_same_odd_part_pair xs with
    | Some (a, b) => build_witness_from_collision a b
    | None => Pdwr_no_collision_found
    end
  else Pdwr_invalid_input.

End Extraction_Interface.

Set Extraction Output Directory "T000_Extraction".
Extraction Language OCaml.

Extraction "OddPartComputations.ml"
  odd_part_aux
  odd_part
  val2_aux
  val2
  odd_part_data
  odd_part_profile
  odd_range_as_nat_list
  odd_part_image
  all_odd_parts_in_rangeb.

Extraction "PigeonholeDivisibilityWitness.ml"
  odd_part
  odd_range_as_nat_list
  member_natb
  same_odd_partb
  dividesb
  valid_pigeonhole_instanceb
  find_same_odd_part_pair
  search_pigeonhole_divisibility_witness.

(*************************************************************************)
(*                                                                       *)
(*  KEY ASSUMPTION REPORT                                                *)
(*                                                                       *)
(*  T000 is intended to be fully closed.  The reports below keep that    *)
(*  visible in the sanctioned build output.                              *)
(*                                                                       *)
(*************************************************************************)

Print Assumptions same_odd_part_divides.
Print Assumptions pigeonhole.
Print Assumptions pigeonhole_divisibility.
