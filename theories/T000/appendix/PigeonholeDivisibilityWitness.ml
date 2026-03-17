
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

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
  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val even : nat -> bool **)

  let rec even = function
  | O -> True
  | S n0 -> (match n0 with
             | O -> False
             | S n' -> even n')

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))
 end

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

(** val odd_range : nat -> nat list **)

let rec odd_range = function
| O -> Nil
| S n' -> app (odd_range n') (Cons ((add (mul (S (S O)) n') (S O)), Nil))

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

(** val same_odd_partb : nat -> nat -> bool **)

let same_odd_partb a b =
  Nat.eqb (odd_part a) (odd_part b)

(** val dividesb : nat -> nat -> bool **)

let dividesb a b =
  match a with
  | O -> False
  | S _ -> Nat.eqb (Nat.modulo b a) O

(** val bounded_by_2n : nat -> nat -> bool **)

let bounded_by_2n n a =
  match Nat.leb (S O) a with
  | True -> Nat.leb a (mul (S (S O)) n)
  | False -> False

(** val all_elements_boundedb : nat -> nat list -> bool **)

let rec all_elements_boundedb n = function
| Nil -> True
| Cons (x, xs') ->
  (match bounded_by_2n n x with
   | True -> all_elements_boundedb n xs'
   | False -> False)

(** val all_distinctb : nat list -> bool **)

let rec all_distinctb = function
| Nil -> True
| Cons (x, xs') ->
  (match negb (member_natb x xs') with
   | True -> all_distinctb xs'
   | False -> False)

(** val valid_pigeonhole_instanceb : nat -> nat list -> bool **)

let valid_pigeonhole_instanceb n xs =
  match all_elements_boundedb n xs with
  | True ->
    (match all_distinctb xs with
     | True -> Nat.eqb (length xs) (S n)
     | False -> False)
  | False -> False

(** val find_same_odd_part_partner : nat -> nat list -> nat option **)

let rec find_same_odd_part_partner a = function
| Nil -> None
| Cons (b, xs') ->
  (match same_odd_partb a b with
   | True -> Some b
   | False -> find_same_odd_part_partner a xs')

(** val find_same_odd_part_pair : nat list -> (nat, nat) prod option **)

let rec find_same_odd_part_pair = function
| Nil -> None
| Cons (a, xs') ->
  (match find_same_odd_part_partner a xs' with
   | Some b -> Some (Pair (a, b))
   | None -> find_same_odd_part_pair xs')

type divisibilityDirection =
| Pdw_left_divides_right
| Pdw_right_divides_left

type pigeonholeDivisibilityWitnessResult =
| Pdwr_invalid_input
| Pdwr_no_collision_found
| Pdwr_collision_without_divisibility of nat * nat * nat
| Pdwr_witness of nat * nat * nat * divisibilityDirection

(** val classify_divisibility_direction :
    nat -> nat -> divisibilityDirection option **)

let classify_divisibility_direction a b =
  match dividesb a b with
  | True -> Some Pdw_left_divides_right
  | False ->
    (match dividesb b a with
     | True -> Some Pdw_right_divides_left
     | False -> None)

(** val build_witness_from_collision :
    nat -> nat -> pigeonholeDivisibilityWitnessResult **)

let build_witness_from_collision a b =
  let shared_odd_part = odd_part a in
  (match classify_divisibility_direction a b with
   | Some direction -> Pdwr_witness (a, b, shared_odd_part, direction)
   | None -> Pdwr_collision_without_divisibility (a, b, shared_odd_part))

(** val search_pigeonhole_divisibility_witness :
    nat -> nat list -> pigeonholeDivisibilityWitnessResult **)

let search_pigeonhole_divisibility_witness n xs =
  match valid_pigeonhole_instanceb n xs with
  | True ->
    (match find_same_odd_part_pair xs with
     | Some p -> let Pair (a, b) = p in build_witness_from_collision a b
     | None -> Pdwr_no_collision_found)
  | False -> Pdwr_invalid_input
