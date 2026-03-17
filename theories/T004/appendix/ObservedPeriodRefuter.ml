
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

type 'a option =
| Some of 'a
| None

type 'a list =
| Nil
| Cons of 'a * 'a list

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
 end

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
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f a), (map f t))

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
 end

type bit = bool

type cell = bit

type row = z -> cell

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

(** val bit_to_nat : bit -> nat **)

let bit_to_nat = function
| True -> S O
| False -> O

(** val bit_list_to_nat_list : bit list -> nat list **)

let bit_list_to_nat_list xs =
  map bit_to_nat xs

(** val canonical_window : nat -> nat -> bit list **)

let canonical_window =
  center_window

(** val canonical_window_as_nat : nat -> nat -> nat list **)

let canonical_window_as_nat radius t =
  bit_list_to_nat_list (canonical_window radius t)

(** val nat_list_eqb : nat list -> nat list -> bool **)

let rec nat_list_eqb xs ys =
  match xs with
  | Nil -> (match ys with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (x, xs') ->
    (match ys with
     | Nil -> False
     | Cons (y, ys') ->
       (match Nat.eqb x y with
        | True -> nat_list_eqb xs' ys'
        | False -> False))

type observedPeriodRefuterResult =
| Opr_invalid_period
| Opr_refuted of nat * nat list * nat list
| Opr_not_refuted_upto of nat

(** val observed_windows_match : nat -> nat -> nat -> bool **)

let observed_windows_match radius period t =
  nat_list_eqb (canonical_window_as_nat radius t)
    (canonical_window_as_nat radius (add t period))

(** val observed_period_refutation_at :
    nat -> nat -> nat -> observedPeriodRefuterResult **)

let observed_period_refutation_at radius period t =
  Opr_refuted (t, (canonical_window_as_nat radius t),
    (canonical_window_as_nat radius (add t period)))

(** val first_observed_period_refutation_from :
    nat -> nat -> nat -> nat -> observedPeriodRefuterResult option **)

let rec first_observed_period_refutation_from radius period t fuel =
  match observed_windows_match radius period t with
  | True ->
    (match fuel with
     | O -> None
     | S fuel' ->
       first_observed_period_refutation_from radius period (S t) fuel')
  | False -> Some (observed_period_refutation_at radius period t)

(** val refute_observed_period :
    nat -> nat -> nat -> observedPeriodRefuterResult **)

let refute_observed_period radius period horizon =
  match Nat.eqb period O with
  | True -> Opr_invalid_period
  | False ->
    (match first_observed_period_refutation_from radius period O horizon with
     | Some result -> result
     | None -> Opr_not_refuted_upto horizon)
