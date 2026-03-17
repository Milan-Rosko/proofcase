
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

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n0 -> (match n0 with
             | O -> False
             | S n' -> even n')

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

(** val odd_part_aux : nat -> nat -> nat **)

let rec odd_part_aux fuel n =
  match fuel with
  | O -> n
  | S fuel' ->
    (match Nat.even n with
     | True -> odd_part_aux fuel' (Nat.div2 n)
     | False -> n)

(** val odd_part : nat -> nat **)

let odd_part n =
  odd_part_aux n n

(** val val2_aux : nat -> nat -> nat **)

let rec val2_aux fuel n =
  match fuel with
  | O -> O
  | S fuel' ->
    (match Nat.even n with
     | True -> S (val2_aux fuel' (Nat.div2 n))
     | False -> O)

(** val val2 : nat -> nat **)

let val2 n =
  val2_aux n n

(** val odd_range : nat -> nat list **)

let rec odd_range = function
| O -> Nil
| S n' -> app (odd_range n') (Cons ((add (mul (S (S O)) n') (S O)), Nil))

(** val odd_part_data : nat -> (nat, nat) prod **)

let odd_part_data n =
  Pair ((val2 n), (odd_part n))

(** val odd_part_profile : nat list -> (nat, nat) prod list **)

let odd_part_profile xs =
  map odd_part_data xs

(** val odd_range_as_nat_list : nat -> nat list **)

let odd_range_as_nat_list =
  odd_range

(** val member_natb : nat -> nat list -> bool **)

let rec member_natb x = function
| Nil -> False
| Cons (y, ys) ->
  (match Nat.eqb x y with
   | True -> True
   | False -> member_natb x ys)

(** val odd_part_image : nat list -> nat list **)

let odd_part_image xs =
  map odd_part xs

(** val all_members_ofb : nat list -> nat list -> bool **)

let rec all_members_ofb cats = function
| Nil -> True
| Cons (x, xs') ->
  (match member_natb x cats with
   | True -> all_members_ofb cats xs'
   | False -> False)

(** val all_odd_parts_in_rangeb : nat -> nat list -> bool **)

let all_odd_parts_in_rangeb n xs =
  all_members_ofb (odd_range_as_nat_list n) (odd_part_image xs)
