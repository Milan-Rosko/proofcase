
type bool =
| True
| False

val xorb : bool -> bool -> bool

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

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

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

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val of_succ_nat : nat -> positive

  val eq_dec : positive -> positive -> sumbool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val eqb : z -> z -> bool

  val of_nat : nat -> z

  val eq_dec : z -> z -> sumbool
 end

val z_lt_dec : z -> z -> sumbool

type bit = bool

type cell = bit

type row = z -> cell

type space_time = nat -> row

val rule30 : cell -> cell -> cell -> cell

val step_row : row -> row

val iter_row : nat -> row -> row

val seed_row : row

val canonical_row : nat -> row

val z_segment : z -> nat -> z list

val centered_coords : nat -> z list

val center_window : nat -> nat -> bit list

val window_data : space_time -> nat -> nat -> bit list

val finite_replay_radius : nat -> nat -> nat

val local_seed_window_model : nat -> row

val truncate : nat -> row -> row

val shifted_canonical_trajectory : nat -> space_time

val bit_to_nat : bit -> nat

val bit_list_to_nat_list : bit list -> nat list

val row_window : row -> nat -> bit list

val row_window_as_nat : row -> nat -> nat list

val seed_window : nat -> bit list

val seed_window_as_nat : nat -> nat list

val canonical_value : nat -> z -> bit

val canonical_value_as_nat : nat -> z -> nat

val trajectory_window : space_time -> nat -> nat -> bit list

val trajectory_windows_from : space_time -> nat -> nat -> nat -> bit list list

val trajectory_prefix_windows : space_time -> nat -> nat -> bit list list

val trajectory_prefix_windows_as_nat :
  space_time -> nat -> nat -> nat list list

val canonical_window : nat -> nat -> bit list

val canonical_window_as_nat : nat -> nat -> nat list

val canonical_prefix_windows : nat -> nat -> bit list list

val canonical_prefix_windows_as_nat : nat -> nat -> nat list list

val shifted_canonical_window : nat -> nat -> nat -> bit list

val shifted_canonical_window_as_nat : nat -> nat -> nat -> nat list

val shifted_canonical_prefix_windows : nat -> nat -> nat -> bit list list

val shifted_canonical_prefix_windows_as_nat :
  nat -> nat -> nat -> nat list list

val local_seed_window_model_window : nat -> nat -> bit list

val local_seed_window_model_window_as_nat : nat -> nat -> nat list

val truncated_canonical_window : nat -> nat -> nat -> bit list

val truncated_canonical_window_as_nat : nat -> nat -> nat -> nat list

val extracted_finite_replay_radius : nat -> nat -> nat
