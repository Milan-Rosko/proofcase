(* R01__Fibonacci.v *)

From Coq Require Import Arith List Bool PeanoNat.
Import ListNotations.

(*************************************************************************)
(*                                                                       *)
(*  Carryless Pairing — Definitions                                      *)
(*                                                                       *)
(*************************************************************************)

(*
   Fibonacci sequence (structural recursion via pairs).
   This avoids non-structural calls to F (S k).
*)

Fixpoint fib_pair (n : nat) : nat * nat :=
  match n with
  | 0 => (0, 1)
  | S n' =>
      match fib_pair n' with
      | (a, b) => (b, a + b)
      end
  end.

Definition F (n : nat) : nat := fst (fib_pair n).

(*
   Sum of Fibonacci values over a list of indices.
*)

Fixpoint sumF (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | k :: xs' => F k + sumF xs'
  end.

(*
   Basic arithmetic helpers.
*)

Definition two (n : nat) : nat := n + n.

Definition two_j_minus1 (j : nat) : nat := Nat.pred (two j). 

Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S k) => is_even k
  end.

Definition is_odd (n : nat) : bool := negb (is_even n).

Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S k) => S (div2 k)
  end.

(*
   Settings of the device:
   (i) Z : Zeckendorf support extractor
   (ii) r : rank (first Fibonacci index strictly above x)
*)

Record Params : Type :=
  {
    Z : nat -> list nat;
    r : nat -> nat
  }.

(*
   Band offset: B(x) = 2 * r(x).
*)

Definition B (P : Params) (x : nat) : nat := 2 * r P x.

(*
   Even/Odd band encodings.
*)

Definition even_band (P : Params) (x : nat) : list nat :=
  map (fun e => two e) (Z P x).

Definition odd_band (P : Params) (x y : nat) : list nat :=
  map (fun j => B P x + two_j_minus1 j) (Z P y).

(*
   Carryless pairing:
   pair x y := sumF (even_band x ++ odd_band x y).
*)

Definition pair (P : Params) (x y : nat) : nat :=
  sumF (even_band P x ++ odd_band P x y).

(*
   Unpairing infrastructure.
*)

Definition half_even_indices (zn : list nat) : list nat :=
  map div2 (filter is_even zn).

Definition odd_ge_B1 (Bx k : nat) : bool :=
  match is_odd k with
  | false => false
  | true => Nat.leb (S Bx) k
  end.

Definition decode_odd_index (Bx k : nat) : nat :=
  div2 (S (k - Bx)).

Definition y_indices (Bx : nat) (zn : list nat) : list nat :=
  map (decode_odd_index Bx) (filter (odd_ge_B1 Bx) zn).

(*
   Carryless unpairing.
*)

Definition unpair (P : Params) (n : nat) : nat * nat :=
  let zn := Z P n in
  let x := sumF (half_even_indices zn) in
  let Bx := B P x in
  let y := sumF (y_indices Bx zn) in
  (x, y).