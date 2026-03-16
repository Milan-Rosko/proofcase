
type bool =
| True
| False

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> False
             | False -> True)
  | False -> b2

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

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

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> False)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> False)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> Right)
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

type bit = bool

type cell = bit

type row = z -> cell

type space_time = nat -> row

(** val rule30 : cell -> cell -> cell -> cell **)

let rule30 a b c =
  xorb a (match b with
          | True -> True
          | False -> c)

(** val step_row : row -> row **)

let step_row r x =
  rule30 (r (Z.sub x (Zpos XH))) (r x) (r (Z.add x (Zpos XH)))

(** val iter_row : nat -> row -> row **)

let rec iter_row n r =
  match n with
  | O -> r
  | S n' -> step_row (iter_row n' r)

(** val seed_row : row **)

let seed_row x =
  Z.eqb x Z0

(** val canonical_row : nat -> row **)

let canonical_row t =
  iter_row t seed_row

(** val z_segment : z -> nat -> z list **)

let rec z_segment start = function
| O -> Nil
| S len' -> Cons (start, (z_segment (Z.add start (Zpos XH)) len'))

(** val centered_coords : nat -> z list **)

let centered_coords n =
  z_segment (Z.opp (Z.of_nat n)) (S (mul (S (S O)) n))

(** val center_window : nat -> nat -> bit list **)

let center_window n t =
  map (canonical_row t) (centered_coords n)

(** val window_data : space_time -> nat -> nat -> bit list **)

let window_data u n t =
  map (u t) (centered_coords n)

(** val finite_replay_radius : nat -> nat -> nat **)

let finite_replay_radius =
  add

(** val local_seed_window_model : nat -> row **)

let local_seed_window_model r x =
  match z_lt_dec x (Z.sub (Z.opp (Z.of_nat r)) (Zpos XH)) with
  | Left -> False
  | Right ->
    (match z_lt_dec (Z.add (Z.of_nat r) (Zpos XH)) x with
     | Left -> False
     | Right ->
       (match Z.eq_dec x (Zneg XH) with
        | Left -> False
        | Right ->
          (match Z.eq_dec x (Z.of_nat r) with
           | Left -> False
           | Right -> True)))

(** val truncate : nat -> row -> row **)

let truncate n u x =
  match match Z.leb (Z.opp (Z.of_nat n)) x with
        | True -> Z.leb x (Z.of_nat n)
        | False -> False with
  | True -> u x
  | False -> False

(** val shifted_canonical_trajectory : nat -> space_time **)

let shifted_canonical_trajectory p t =
  canonical_row (add t p)

(** val bit_to_nat : bit -> nat **)

let bit_to_nat = function
| True -> S O
| False -> O

(** val bit_list_to_nat_list : bit list -> nat list **)

let bit_list_to_nat_list xs =
  map bit_to_nat xs

(** val row_window : row -> nat -> bit list **)

let row_window r radius =
  map r (centered_coords radius)

(** val row_window_as_nat : row -> nat -> nat list **)

let row_window_as_nat r radius =
  bit_list_to_nat_list (row_window r radius)

(** val seed_window : nat -> bit list **)

let seed_window radius =
  row_window seed_row radius

(** val seed_window_as_nat : nat -> nat list **)

let seed_window_as_nat radius =
  row_window_as_nat seed_row radius

(** val canonical_value : nat -> z -> bit **)

let canonical_value =
  canonical_row

(** val canonical_value_as_nat : nat -> z -> nat **)

let canonical_value_as_nat t x =
  bit_to_nat (canonical_value t x)

(** val trajectory_window : space_time -> nat -> nat -> bit list **)

let trajectory_window =
  window_data

(** val trajectory_windows_from :
    space_time -> nat -> nat -> nat -> bit list list **)

let rec trajectory_windows_from u radius start = function
| O -> Nil
| S len' ->
  Cons ((trajectory_window u radius start),
    (trajectory_windows_from u radius (S start) len'))

(** val trajectory_prefix_windows :
    space_time -> nat -> nat -> bit list list **)

let trajectory_prefix_windows u radius height =
  trajectory_windows_from u radius O (S height)

(** val trajectory_prefix_windows_as_nat :
    space_time -> nat -> nat -> nat list list **)

let trajectory_prefix_windows_as_nat u radius height =
  map bit_list_to_nat_list (trajectory_prefix_windows u radius height)

(** val canonical_window : nat -> nat -> bit list **)

let canonical_window =
  center_window

(** val canonical_window_as_nat : nat -> nat -> nat list **)

let canonical_window_as_nat radius t =
  bit_list_to_nat_list (canonical_window radius t)

(** val canonical_prefix_windows : nat -> nat -> bit list list **)

let canonical_prefix_windows radius height =
  trajectory_prefix_windows canonical_row radius height

(** val canonical_prefix_windows_as_nat : nat -> nat -> nat list list **)

let canonical_prefix_windows_as_nat radius height =
  trajectory_prefix_windows_as_nat canonical_row radius height

(** val shifted_canonical_window : nat -> nat -> nat -> bit list **)

let shifted_canonical_window period radius t =
  trajectory_window (shifted_canonical_trajectory period) radius t

(** val shifted_canonical_window_as_nat : nat -> nat -> nat -> nat list **)

let shifted_canonical_window_as_nat period radius t =
  bit_list_to_nat_list (shifted_canonical_window period radius t)

(** val shifted_canonical_prefix_windows :
    nat -> nat -> nat -> bit list list **)

let shifted_canonical_prefix_windows period radius height =
  trajectory_prefix_windows (shifted_canonical_trajectory period) radius
    height

(** val shifted_canonical_prefix_windows_as_nat :
    nat -> nat -> nat -> nat list list **)

let shifted_canonical_prefix_windows_as_nat period radius height =
  trajectory_prefix_windows_as_nat (shifted_canonical_trajectory period)
    radius height

(** val local_seed_window_model_window : nat -> nat -> bit list **)

let local_seed_window_model_window seed_radius window_radius =
  row_window (local_seed_window_model seed_radius) window_radius

(** val local_seed_window_model_window_as_nat : nat -> nat -> nat list **)

let local_seed_window_model_window_as_nat seed_radius window_radius =
  bit_list_to_nat_list
    (local_seed_window_model_window seed_radius window_radius)

(** val truncated_canonical_window : nat -> nat -> nat -> bit list **)

let truncated_canonical_window truncate_radius t window_radius =
  row_window (truncate truncate_radius (canonical_row t)) window_radius

(** val truncated_canonical_window_as_nat : nat -> nat -> nat -> nat list **)

let truncated_canonical_window_as_nat truncate_radius t window_radius =
  bit_list_to_nat_list
    (truncated_canonical_window truncate_radius t window_radius)

(** val extracted_finite_replay_radius : nat -> nat -> nat **)

let extracted_finite_replay_radius =
  finite_replay_radius
