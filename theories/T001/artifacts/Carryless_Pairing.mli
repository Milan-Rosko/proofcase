
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val pred : nat -> nat

  val leb : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val fib_pair : nat -> (nat, nat) prod

val f : nat -> nat

val sumF : nat list -> nat

val two : nat -> nat

val two_j_minus1 : nat -> nat

val is_even : nat -> bool

val is_odd : nat -> bool

val div2 : nat -> nat

type params = { z : (nat -> nat list); r : (nat -> nat) }

val b : params -> nat -> nat

val even_band : params -> nat -> nat list

val odd_band : params -> nat -> nat -> nat list

val pair : params -> nat -> nat -> nat

val half_even_indices : nat list -> nat list

val odd_ge_B1 : nat -> nat -> bool

val decode_odd_index : nat -> nat -> nat

val y_indices : nat -> nat list -> nat list

val unpair : params -> nat -> (nat, nat) prod
