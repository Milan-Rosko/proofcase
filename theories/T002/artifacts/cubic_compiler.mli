
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

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

module Nat :
 sig
  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val max : nat -> nat -> nat
 end

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val firstn : nat -> 'a1 list -> 'a1 list

type expr =
| Const of nat
| Var of nat
| Add of expr * expr
| Sub of expr * expr
| Mul of expr * expr

val degree : expr -> nat

type form =
| F_Bot
| F_Imp of form * form

val bot : form

val form_eqb : form -> form -> bool

val is_K : form -> bool

val is_EFQ : form -> bool

val is_S : form -> bool

val is_axiom : form -> bool

type proof = form list

val existsb_local : ('a1 -> bool) -> 'a1 list -> bool

val mp_witness : form list -> form -> bool

val check_lines : form list -> proof -> bool

val last_opt : proof -> form option

val fib_pair : nat -> (nat, nat) prod

val f : nat -> nat

type assignment = { as_pf : proof; as_target : form; as_c : nat; as_d : nat }

type constraint0 =
| C_Axiom of nat
| C_MP of nat * nat * nat
| C_Justification of nat
| C_Target

val p_axiom : assignment -> nat -> expr

val line_at : assignment -> nat -> form

val axiom_okb : assignment -> nat -> bool

val mp_okb : assignment -> nat -> nat -> nat -> bool

val justification_okb : assignment -> nat -> bool

val target_okb : assignment -> bool

val constraint_holdsb : assignment -> constraint0 -> bool

val just_constraints_from_pf : nat -> proof -> constraint0 list

val system_constraints : assignment -> constraint0 list

val p_MP : assignment -> nat -> expr

val p_target : proof -> form -> expr

type polynomial = { poly_expr : expr; poly_eval : (assignment -> nat) }

val bool_zero : bool -> nat

val degree_witness_assignment : assignment

val constraint_poly_expr : constraint0 -> expr

val poly_of_constraint : constraint0 -> polynomial

val polynomial_system : assignment -> polynomial list

val fib : nat -> nat

val zero_poly : polynomial

val split_posneg : polynomial -> (polynomial, polynomial) prod

val band_width : nat

val band_index : nat -> nat -> nat

val fib_weight : nat -> nat -> nat

val banded_channel_expr : nat -> nat -> polynomial list -> expr

val banded_channel_eval : nat -> nat -> polynomial list -> assignment -> nat

val capacity_bound : nat -> nat

val banded_eq_aggregate_with :
  nat -> (polynomial, polynomial) prod list -> (polynomial, polynomial) prod

val split_system_equations :
  polynomial list -> (polynomial, polynomial) prod list

val split_left_channels : polynomial list -> polynomial list

val split_right_channels : polynomial list -> polynomial list

val split_channels : polynomial list -> polynomial list

val banded_main_equation_with :
  nat -> polynomial list -> (polynomial, polynomial) prod

val capacity_poly_expr : nat -> polynomial -> expr

val capacity_poly_eval : nat -> polynomial -> assignment -> nat

val capacity_poly : nat -> polynomial -> polynomial

val capacity_eq : nat -> polynomial -> (polynomial, polynomial) prod

val capacity_equations_with :
  nat -> polynomial list -> (polynomial, polynomial) prod list

val all_banded_equations_with :
  nat -> polynomial list -> (polynomial, polynomial) prod list

val banded_single_equation_with :
  nat -> polynomial list -> (polynomial, polynomial) prod

val banded_single_equation_for_system :
  polynomial list -> (polynomial, polynomial) prod

val canonical_assignment : proof -> form -> assignment

val emit_cubic_system : proof -> form -> polynomial list

val emit_single_cubic : proof -> form -> (polynomial, polynomial) prod
