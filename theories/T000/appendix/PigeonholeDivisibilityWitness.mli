
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val even : nat -> bool

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val modulo : nat -> nat -> nat

  val div2 : nat -> nat
 end

val odd_part_aux : nat -> nat -> nat

val odd_part : nat -> nat

val odd_range : nat -> nat list

val odd_range_as_nat_list : nat -> nat list

val member_natb : nat -> nat list -> bool

val same_odd_partb : nat -> nat -> bool

val dividesb : nat -> nat -> bool

val bounded_by_2n : nat -> nat -> bool

val all_elements_boundedb : nat -> nat list -> bool

val all_distinctb : nat list -> bool

val valid_pigeonhole_instanceb : nat -> nat list -> bool

val find_same_odd_part_partner : nat -> nat list -> nat option

val find_same_odd_part_pair : nat list -> (nat, nat) prod option

type divisibilityDirection =
| Pdw_left_divides_right
| Pdw_right_divides_left

type pigeonholeDivisibilityWitnessResult =
| Pdwr_invalid_input
| Pdwr_no_collision_found
| Pdwr_collision_without_divisibility of nat * nat * nat
| Pdwr_witness of nat * nat * nat * divisibilityDirection

val classify_divisibility_direction :
  nat -> nat -> divisibilityDirection option

val build_witness_from_collision :
  nat -> nat -> pigeonholeDivisibilityWitnessResult

val search_pigeonhole_divisibility_witness :
  nat -> nat list -> pigeonholeDivisibilityWitnessResult
