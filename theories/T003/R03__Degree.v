(* R03__Degree.v *)

From Coq Require Import ZArith List Bool Arith Lia.
Import ListNotations.

From T003 Require Import R02__Coefficients R01__Coeff_types.

Fixpoint sum_exps (xs : list (nat * nat)) : nat :=
  match xs with
  | [] => 0
  | (_, e) :: xs' => e + sum_exps xs'
  end.

Fixpoint exps_ok (xs : list (nat * nat)) : bool :=
  match xs with
  | [] => true
  | (_, e) :: xs' => Nat.leb e 3 && exps_ok xs'
  end.

Definition monom_deg_ok (m : monom) : bool :=
  exps_ok m.(exps) && Nat.leb (sum_exps m.(exps)) 3.

Fixpoint poly_deg_ok (p : list monom) : bool :=
  match p with
  | [] => true
  | m :: p' => monom_deg_ok m && poly_deg_ok p'
  end.

Definition deg_ok : bool := poly_deg_ok poly.

Theorem degree_le_3 : deg_ok = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Definition monom_degree (m : monom) : nat := sum_exps m.(exps).
Definition degrees : list nat := map monom_degree poly.
Definition max_degree : nat := fold_left Nat.max degrees 0%nat.
Definition has_degree_3 : bool := existsb (Nat.eqb 3%nat) degrees.
Definition count_degree_3 : nat := length (filter (Nat.eqb 3%nat) degrees).

Theorem max_degree_eq_3 : max_degree = 3%nat.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem has_degree_3_true : has_degree_3 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Theorem degree_at_most_3 : (max_degree <= 3)%nat.
Proof.
  rewrite max_degree_eq_3.
  lia.
Qed.
