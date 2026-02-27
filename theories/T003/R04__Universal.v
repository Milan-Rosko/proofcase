(* R04__Universal.v *)

From Coq Require Import ZArith List String Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

From T003 Require Import
  R00__VarMap
  R01__Coeff_types
  R02__Coefficients
  R03__Degree
  R07__Table_Inspection.
Definition env := nat -> Z.

(*
  Trust boundary:
  - U_table is the pinned bounded universal cubic polynomial artifact.
  - The Python constructor + lockfile are the ground truth for this artifact.
  - table_digest_ok is the kernel-checked inspection gate over the actual table.
*)

Definition U_table (rho : env) : Z := R02__Coefficients.U rho.
Definition U (rho : env) : Z := U_table rho.

(* Keep giant table constants opaque in this interface layer. *)
Local Opaque R02__Coefficients.poly R02__Coefficients.U.

Record UniversalCubic := {
  uc_poly : list monom;
  uc_U : env -> Z;
  uc_ix_u : nat;
  uc_digest_ok : table_digest_of uc_poly = table_digest_expected
}.

Definition UC : UniversalCubic := {|
  uc_poly := R02__Coefficients.poly;
  uc_U := U_table;
  uc_ix_u := ix_u;
  uc_digest_ok := table_digest_ok
|}.

Definition eval_poly_table (rho : env) : Z := U_table rho.
Definition eval_poly (rho : env) : Z := eval_poly_table rho.

Definition bounded_n_lines : nat := bound_n_lines.
Definition bounded_digit_width : nat := bound_digit_width.
Definition bounded_max_repr_lane : nat := bound_max_repr_lane.
Definition bounded_max_repr_full : nat := bound_max_repr_full.

Definition cubic_sat_env (rho : env) : Prop :=
  eval_poly rho = 0.

Definition env_nonneg (rho : env) : Prop :=
  forall i, 0 <= rho i.

Definition cubic_sat_env_N (rho : env) : Prop :=
  env_nonneg rho /\ cubic_sat_env rho.

Definition cubic_sat_list (xs : list Z) : Prop :=
  List.length xs = var_count /\
  eval_poly (fun i => nth_default 0%Z xs i) = 0.

Definition cubic_sat_list_N (xs : list Z) : Prop :=
  List.length xs = var_count /\
  Forall (fun z => 0 <= z) xs /\
  eval_poly (fun i => nth_default 0%Z xs i) = 0.

Lemma cubic_sat_list_env :
  forall xs,
    cubic_sat_list xs ->
    cubic_sat_env (fun i => nth_default 0%Z xs i).
Proof.
  intros xs [Hlen Heq].
  exact Heq.
Qed.

Lemma cubic_sat_list_N_env :
  forall xs,
    cubic_sat_list_N xs ->
    cubic_sat_env_N (fun i => nth_default 0%Z xs i).
Proof.
  intros xs [Hlen [Hall Heq]].
  split.
  - intro i.
    unfold nth_default.
    destruct (nth_error xs i) as [x|] eqn:Hnth.
    + pose proof (proj1 (Forall_forall (fun z : Z => 0 <= z) xs) Hall) as Hforall.
      apply Hforall.
      now apply nth_error_In with (n := i).
    + lia.
  - exact Heq.
Qed.

Theorem cubic_degree_le_3 :
  deg_ok = true.
Proof.
  exact degree_le_3.
Qed.

Record universal_cubic := {
  uc_var_count : nat;
  uc_base      : Z;
  uc_channel_count : nat;
  uc_bound_n_lines : nat;
  uc_bound_digit_width : nat;
  uc_bound_max_repr_lane : nat;
  uc_bound_max_repr_full : nat;
  uc_max_coeff_digits : nat;

  (*
    Hash of the coefficient-table artifact (U_table).
  *)

  uc_coeff_hash : string;
  uc_degree_ok : deg_ok = true;
  uc_has_degree_3 : has_degree_3 = true;
  uc_max_degree_eq_3 : max_degree = 3%nat
}.

Definition universal : universal_cubic := {|
  uc_var_count := var_count;
  uc_base := base;
  uc_channel_count := channel_count;
  uc_bound_n_lines := bounded_n_lines;
  uc_bound_digit_width := bounded_digit_width;
  uc_bound_max_repr_lane := bounded_max_repr_lane;
  uc_bound_max_repr_full := bounded_max_repr_full;
  uc_max_coeff_digits := max_coeff_digits;
  uc_coeff_hash := coeff_hash;
  uc_degree_ok := degree_le_3;
  uc_has_degree_3 := has_degree_3_true;
  uc_max_degree_eq_3 := max_degree_eq_3
|}.

Theorem U_degree_3 : deg_ok = true.
Proof. exact degree_le_3. Qed.
