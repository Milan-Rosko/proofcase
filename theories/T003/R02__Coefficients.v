From Coq Require Import ZArith List String.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

From T003 Require Import R01__Coeff_types.
From T003.Chunks Require Import Coeff_chunk_0.
From T003.Chunks Require Import Coeff_chunk_1.
From T003.Chunks Require Import Coeff_chunk_2.
From T003.Chunks Require Import Coeff_chunk_3.
From T003.Chunks Require Import Coeff_chunk_4.
From T003.Chunks Require Import Coeff_chunk_5.
From T003.Chunks Require Import Coeff_chunk_6.
From T003.Chunks Require Import Coeff_chunk_7.
From T003.Chunks Require Import Coeff_chunk_8.
From T003.Chunks Require Import Coeff_chunk_9.
From T003.Chunks Require Import Coeff_chunk_10.
From T003.Chunks Require Import Coeff_chunk_11.
From T003.Chunks Require Import Coeff_chunk_12.
From T003.Chunks Require Import Coeff_chunk_13.
From T003.Chunks Require Import Coeff_chunk_14.
From T003.Chunks Require Import Coeff_chunk_15.
From T003.Chunks Require Import Coeff_chunk_16.
From T003.Chunks Require Import Coeff_chunk_17.
From T003.Chunks Require Import Coeff_chunk_18.
From T003.Chunks Require Import Coeff_chunk_19.

Definition poly : list monom := poly_chunk_0 ++ poly_chunk_1 ++ poly_chunk_2 ++ poly_chunk_3 ++ poly_chunk_4 ++ poly_chunk_5 ++ poly_chunk_6 ++ poly_chunk_7 ++ poly_chunk_8 ++ poly_chunk_9 ++ poly_chunk_10 ++ poly_chunk_11 ++ poly_chunk_12 ++ poly_chunk_13 ++ poly_chunk_14 ++ poly_chunk_15 ++ poly_chunk_16 ++ poly_chunk_17 ++ poly_chunk_18 ++ poly_chunk_19.

Definition eval_monom (rho : nat -> Z) (m : monom) : Z :=
  m.(coeff)
  * fold_left
      (fun acc ve =>
         let '(v, e) := ve in acc * (rho v) ^ (Z.of_nat e))
      m.(exps) 1.
Definition U (rho : nat -> Z) : Z := fold_left (fun acc m => acc + eval_monom rho m) poly 0.
