
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

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

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))
 end

(** val nth : nat -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l default =
  match n with
  | O -> (match l with
          | Nil -> default
          | Cons (x, _) -> x)
  | S m -> (match l with
            | Nil -> default
            | Cons (_, t) -> nth m t default)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f0 = function
| Nil -> Nil
| Cons (a, t) -> Cons ((f0 a), (map f0 t))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n l =
  match n with
  | O -> Nil
  | S n0 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n0 l0)))

type expr =
| Const of nat
| Var of nat
| Add of expr * expr
| Sub of expr * expr
| Mul of expr * expr

(** val degree : expr -> nat **)

let rec degree = function
| Const _ -> O
| Var _ -> S O
| Add (a, b) -> Nat.max (degree a) (degree b)
| Sub (a, b) -> Nat.max (degree a) (degree b)
| Mul (a, b) -> add (degree a) (degree b)

type form =
| F_Bot
| F_Imp of form * form

(** val bot : form **)

let bot =
  F_Bot

(** val form_eqb : form -> form -> bool **)

let rec form_eqb a b =
  match a with
  | F_Bot -> (match b with
              | F_Bot -> True
              | F_Imp (_, _) -> False)
  | F_Imp (a1, a2) ->
    (match b with
     | F_Bot -> False
     | F_Imp (b1, b2) ->
       (match form_eqb a1 b1 with
        | True -> form_eqb a2 b2
        | False -> False))

(** val is_K : form -> bool **)

let is_K = function
| F_Bot -> False
| F_Imp (a, f0) ->
  (match f0 with
   | F_Bot -> False
   | F_Imp (_, a') -> form_eqb a a')

(** val is_EFQ : form -> bool **)

let is_EFQ = function
| F_Bot -> False
| F_Imp (f0, _) -> (match f0 with
                    | F_Bot -> True
                    | F_Imp (_, _) -> False)

(** val is_S : form -> bool **)

let is_S = function
| F_Bot -> False
| F_Imp (f0, f1) ->
  (match f0 with
   | F_Bot -> False
   | F_Imp (a, f2) ->
     (match f2 with
      | F_Bot -> False
      | F_Imp (b, c) ->
        (match f1 with
         | F_Bot -> False
         | F_Imp (f3, f4) ->
           (match f3 with
            | F_Bot -> False
            | F_Imp (a1, b1) ->
              (match f4 with
               | F_Bot -> False
               | F_Imp (a2, c2) ->
                 (match match form_eqb a a1 with
                        | True -> form_eqb a a2
                        | False -> False with
                  | True ->
                    (match form_eqb b b1 with
                     | True -> form_eqb c c2
                     | False -> False)
                  | False -> False))))))

(** val is_axiom : form -> bool **)

let is_axiom phi =
  match is_EFQ phi with
  | True -> True
  | False -> (match is_K phi with
              | True -> True
              | False -> is_S phi)

type proof = form list

(** val existsb_local : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb_local p = function
| Nil -> False
| Cons (x, xs') ->
  (match p x with
   | True -> True
   | False -> existsb_local p xs')

(** val mp_witness : form list -> form -> bool **)

let mp_witness ctx phi =
  existsb_local (fun psi ->
    existsb_local (fun chi ->
      match chi with
      | F_Bot -> False
      | F_Imp (x, y) ->
        (match form_eqb x psi with
         | True -> form_eqb y phi
         | False -> False)) ctx) ctx

(** val check_lines : form list -> proof -> bool **)

let rec check_lines ctx = function
| Nil -> True
| Cons (line, rest) ->
  let ok_line =
    match is_axiom line with
    | True -> True
    | False -> mp_witness ctx line
  in
  (match ok_line with
   | True -> check_lines (Cons (line, ctx)) rest
   | False -> False)

(** val last_opt : proof -> form option **)

let rec last_opt = function
| Nil -> None
| Cons (x, xs) -> (match xs with
                   | Nil -> Some x
                   | Cons (_, _) -> last_opt xs)

(** val fib_pair : nat -> (nat, nat) prod **)

let rec fib_pair = function
| O -> Pair (O, (S O))
| S n' -> let Pair (a, b) = fib_pair n' in Pair (b, (add a b))

(** val f : nat -> nat **)

let f n =
  fst (fib_pair n)

type assignment = { as_pf : proof; as_target : form; as_c : nat; as_d : nat }

type constraint0 =
| C_Axiom of nat
| C_MP of nat * nat * nat
| C_Justification of nat
| C_Target

(** val p_axiom : assignment -> nat -> expr **)

let p_axiom _ _ =
  Mul ((Var O), (Var (S O)))

(** val line_at : assignment -> nat -> form **)

let line_at a i =
  nth i a.as_pf bot

(** val axiom_okb : assignment -> nat -> bool **)

let axiom_okb a i =
  match Nat.ltb i (length a.as_pf) with
  | True -> is_axiom (line_at a i)
  | False -> False

(** val mp_okb : assignment -> nat -> nat -> nat -> bool **)

let mp_okb a i j k =
  match Nat.ltb j i with
  | True ->
    (match Nat.ltb k i with
     | True ->
       (match line_at a k with
        | F_Bot -> False
        | F_Imp (x, y) ->
          (match form_eqb x (line_at a j) with
           | True -> form_eqb y (line_at a i)
           | False -> False))
     | False -> False)
  | False -> False

(** val justification_okb : assignment -> nat -> bool **)

let justification_okb a i =
  match Nat.ltb i (length a.as_pf) with
  | True -> check_lines Nil (firstn (S i) a.as_pf)
  | False -> False

(** val target_okb : assignment -> bool **)

let target_okb a =
  match last_opt a.as_pf with
  | Some last -> form_eqb last a.as_target
  | None -> False

(** val constraint_holdsb : assignment -> constraint0 -> bool **)

let constraint_holdsb a = function
| C_Axiom i -> axiom_okb a i
| C_MP (i, j, k) -> mp_okb a i j k
| C_Justification i -> justification_okb a i
| C_Target -> target_okb a

(** val just_constraints_from_pf : nat -> proof -> constraint0 list **)

let rec just_constraints_from_pf i = function
| Nil -> Nil
| Cons (_, rest) ->
  Cons ((C_Justification i), (just_constraints_from_pf (S i) rest))

(** val system_constraints : assignment -> constraint0 list **)

let system_constraints a =
  Cons (C_Target, (just_constraints_from_pf O a.as_pf))

(** val p_MP : assignment -> nat -> expr **)

let p_MP _ _ =
  Mul ((Var O), (Mul ((Var (S O)), (Var (S (S O))))))

(** val p_target : proof -> form -> expr **)

let p_target _ _ =
  Mul ((Var O), (Var (S O)))

type polynomial = { poly_expr : expr; poly_eval : (assignment -> nat) }

(** val bool_zero : bool -> nat **)

let bool_zero = function
| True -> O
| False -> S O

(** val degree_witness_assignment : assignment **)

let degree_witness_assignment =
  { as_pf = Nil; as_target = F_Bot; as_c = O; as_d = O }

(** val constraint_poly_expr : constraint0 -> expr **)

let constraint_poly_expr = function
| C_Axiom i -> p_axiom degree_witness_assignment i
| C_MP (i, _, _) -> p_MP degree_witness_assignment i
| C_Justification i -> p_MP degree_witness_assignment i
| C_Target -> p_target Nil F_Bot

(** val poly_of_constraint : constraint0 -> polynomial **)

let poly_of_constraint c =
  { poly_expr = (constraint_poly_expr c); poly_eval = (fun a ->
    bool_zero (constraint_holdsb a c)) }

(** val polynomial_system : assignment -> polynomial list **)

let polynomial_system a =
  map poly_of_constraint (system_constraints a)

(** val fib : nat -> nat **)

let fib =
  f

(** val zero_poly : polynomial **)

let zero_poly =
  { poly_expr = (Const O); poly_eval = (fun _ -> O) }

(** val split_posneg : polynomial -> (polynomial, polynomial) prod **)

let split_posneg p =
  Pair (p, zero_poly)

(** val band_width : nat **)

let band_width =
  S (S (S (S O)))

(** val band_index : nat -> nat -> nat **)

let band_index k i =
  add (S (S O)) (mul i k)

(** val fib_weight : nat -> nat -> nat **)

let fib_weight k i =
  fib (band_index k i)

(** val banded_channel_expr : nat -> nat -> polynomial list -> expr **)

let rec banded_channel_expr k i = function
| Nil -> Const O
| Cons (p, ps') ->
  Add ((Mul ((Const (fib_weight k i)), p.poly_expr)),
    (banded_channel_expr k (S i) ps'))

(** val banded_channel_eval :
    nat -> nat -> polynomial list -> assignment -> nat **)

let rec banded_channel_eval k i ps a =
  match ps with
  | Nil -> O
  | Cons (p, ps') ->
    add (mul (fib_weight k i) (p.poly_eval a))
      (banded_channel_eval k (S i) ps' a)

(** val capacity_bound : nat -> nat **)

let capacity_bound k =
  fib (S k)

(** val banded_eq_aggregate_with :
    nat -> (polynomial, polynomial) prod list -> (polynomial, polynomial) prod **)

let banded_eq_aggregate_with k eqs =
  Pair ({ poly_expr = (banded_channel_expr k O (map fst eqs)); poly_eval =
    (fun a -> banded_channel_eval k O (map fst eqs) a) }, { poly_expr =
    (banded_channel_expr k O (map snd eqs)); poly_eval = (fun a ->
    banded_channel_eval k O (map snd eqs) a) })

(** val split_system_equations :
    polynomial list -> (polynomial, polynomial) prod list **)

let split_system_equations sys =
  map split_posneg sys

(** val split_left_channels : polynomial list -> polynomial list **)

let split_left_channels sys =
  map fst (split_system_equations sys)

(** val split_right_channels : polynomial list -> polynomial list **)

let split_right_channels sys =
  map snd (split_system_equations sys)

(** val split_channels : polynomial list -> polynomial list **)

let split_channels sys =
  app (split_left_channels sys) (split_right_channels sys)

(** val banded_main_equation_with :
    nat -> polynomial list -> (polynomial, polynomial) prod **)

let banded_main_equation_with k sys =
  banded_eq_aggregate_with k (split_system_equations sys)

(** val capacity_poly_expr : nat -> polynomial -> expr **)

let capacity_poly_expr k c =
  Sub (c.poly_expr, (Const (sub (capacity_bound k) (S O))))

(** val capacity_poly_eval : nat -> polynomial -> assignment -> nat **)

let capacity_poly_eval k c a =
  sub (c.poly_eval a) (sub (capacity_bound k) (S O))

(** val capacity_poly : nat -> polynomial -> polynomial **)

let capacity_poly k c =
  { poly_expr = (capacity_poly_expr k c); poly_eval =
    (capacity_poly_eval k c) }

(** val capacity_eq : nat -> polynomial -> (polynomial, polynomial) prod **)

let capacity_eq k c =
  Pair ((capacity_poly k c), zero_poly)

(** val capacity_equations_with :
    nat -> polynomial list -> (polynomial, polynomial) prod list **)

let capacity_equations_with k sys =
  map (capacity_eq k) (split_channels sys)

(** val all_banded_equations_with :
    nat -> polynomial list -> (polynomial, polynomial) prod list **)

let all_banded_equations_with k sys =
  Cons ((banded_main_equation_with k sys), (capacity_equations_with k sys))

(** val banded_single_equation_with :
    nat -> polynomial list -> (polynomial, polynomial) prod **)

let banded_single_equation_with k sys =
  banded_eq_aggregate_with k (all_banded_equations_with k sys)

(** val banded_single_equation_for_system :
    polynomial list -> (polynomial, polynomial) prod **)

let banded_single_equation_for_system sys =
  banded_single_equation_with band_width sys

(** val canonical_assignment : proof -> form -> assignment **)

let canonical_assignment pf target =
  { as_pf = pf; as_target = target; as_c = O; as_d = O }

(** val emit_cubic_system : proof -> form -> polynomial list **)

let emit_cubic_system pf target =
  polynomial_system (canonical_assignment pf target)

(** val emit_single_cubic : proof -> form -> (polynomial, polynomial) prod **)

let emit_single_cubic pf target =
  banded_single_equation_for_system (emit_cubic_system pf target)
