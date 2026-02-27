
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

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

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

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f0 a), (map f0 t))

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f0 = function
| Nil -> Nil
| Cons (x, l0) ->
  (match f0 x with
   | True -> Cons (x, (filter f0 l0))
   | False -> filter f0 l0)

(** val fib_pair : nat -> (nat, nat) prod **)

let rec fib_pair = function
| O -> Pair (O, (S O))
| S n' -> let Pair (a, b0) = fib_pair n' in Pair (b0, (add a b0))

(** val f : nat -> nat **)

let f n =
  fst (fib_pair n)

(** val sumF : nat list -> nat **)

let rec sumF = function
| Nil -> O
| Cons (k, xs') -> add (f k) (sumF xs')

(** val two : nat -> nat **)

let two n =
  add n n

(** val two_j_minus1 : nat -> nat **)

let two_j_minus1 j =
  Nat.pred (two j)

(** val is_even : nat -> bool **)

let rec is_even = function
| O -> True
| S n0 -> (match n0 with
           | O -> False
           | S k -> is_even k)

(** val is_odd : nat -> bool **)

let is_odd n =
  negb (is_even n)

(** val div2 : nat -> nat **)

let rec div2 = function
| O -> O
| S n0 -> (match n0 with
           | O -> O
           | S k -> S (div2 k))

type params = { z : (nat -> nat list); r : (nat -> nat) }

(** val b : params -> nat -> nat **)

let b p x =
  mul (S (S O)) (p.r x)

(** val even_band : params -> nat -> nat list **)

let even_band p x =
  map two (p.z x)

(** val odd_band : params -> nat -> nat -> nat list **)

let odd_band p x y =
  map (fun j -> add (b p x) (two_j_minus1 j)) (p.z y)

(** val pair : params -> nat -> nat -> nat **)

let pair p x y =
  sumF (app (even_band p x) (odd_band p x y))

(** val half_even_indices : nat list -> nat list **)

let half_even_indices zn =
  map div2 (filter is_even zn)

(** val odd_ge_B1 : nat -> nat -> bool **)

let odd_ge_B1 bx k =
  match is_odd k with
  | True -> Nat.leb (S bx) k
  | False -> False

(** val decode_odd_index : nat -> nat -> nat **)

let decode_odd_index bx k =
  div2 (S (sub k bx))

(** val y_indices : nat -> nat list -> nat list **)

let y_indices bx zn =
  map (decode_odd_index bx) (filter (odd_ge_B1 bx) zn)

(** val unpair : params -> nat -> (nat, nat) prod **)

let unpair p n =
  let zn = p.z n in
  let x = sumF (half_even_indices zn) in
  let bx = b p x in let y = sumF (y_indices bx zn) in Pair (x, y)
