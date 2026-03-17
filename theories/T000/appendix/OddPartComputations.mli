
type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val even : nat -> bool

  val div2 : nat -> nat
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val odd_part_aux : nat -> nat -> nat

val odd_part : nat -> nat

val val2_aux : nat -> nat -> nat

val val2 : nat -> nat

val odd_range : nat -> nat list

val odd_part_data : nat -> (nat, nat) prod

val odd_part_profile : nat list -> (nat, nat) prod list

val odd_range_as_nat_list : nat -> nat list

val member_natb : nat -> nat list -> bool

val odd_part_image : nat list -> nat list

val all_members_ofb : nat list -> nat list -> bool

val all_odd_parts_in_rangeb : nat -> nat list -> bool
