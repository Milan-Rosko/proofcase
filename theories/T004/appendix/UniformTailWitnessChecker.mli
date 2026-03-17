
type bool =
| True
| False

val xorb : bool -> bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type 'a list =
| Nil
| Cons of 'a * 'a list

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

module Nat :
 sig
  val eqb : nat -> nat -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val eqb : z -> z -> bool

  val of_nat : nat -> z
 end

type bit = bool

type cell = bit

type row = z -> cell

val rule30 : cell -> cell -> cell -> cell

val step_row : row -> row

val iter_row : nat -> row -> row

val seed_row : row

val canonical_row : nat -> row

val z_segment : z -> nat -> z list

val centered_coords : nat -> z list

val center_window : nat -> nat -> bit list

val bit_to_nat : bit -> nat

val bit_list_to_nat_list : bit list -> nat list

val canonical_window : nat -> nat -> bit list

val canonical_window_as_nat : nat -> nat -> nat list

val nat_list_eqb : nat list -> nat list -> bool

type uniformTailWitnessCandidate = { utwc_radius : nat; utwc_start : 
                                     nat; utwc_period : nat;
                                     utwc_extra_bound : nat;
                                     utwc_time_bound : nat }

type uniformTailWitnessCheck =
| Utwc_invalid_period
| Utwc_rejected of nat * nat * nat list * nat list
| Utwc_accepts_through of nat * nat

val uniform_tail_window_as_nat :
  uniformTailWitnessCandidate -> nat -> nat -> nat -> nat list

val uniform_tail_witness_matches :
  uniformTailWitnessCandidate -> nat -> nat -> bool

val uniform_tail_witness_rejection :
  uniformTailWitnessCandidate -> nat -> nat -> uniformTailWitnessCheck

val first_uniform_tail_time_failure :
  uniformTailWitnessCandidate -> nat -> nat -> nat -> uniformTailWitnessCheck
  option

val first_uniform_tail_extra_failure :
  uniformTailWitnessCandidate -> nat -> nat -> uniformTailWitnessCheck option

val check_uniform_tail_witness_candidate :
  uniformTailWitnessCandidate -> uniformTailWitnessCheck
