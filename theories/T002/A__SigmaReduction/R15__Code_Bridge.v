(* R15__Code_Bridge.v *)

From Coq Require Import Arith List.
Import ListNotations.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R06__Encoding_Formula_Coding
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker.

From T002 Require Import R14__Reduction_Core.

Definition enc_form_nat : Form -> nat :=
  enc_form.

Fixpoint code_list (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | x :: xs' => S (pair P0 x (code_list xs'))
  end.

Definition code_pf (pf : Proof) : nat :=
  code_list (map enc_form_nat pf).

Definition code_of_concrete (pf : Proof) (target : Form) : nat :=
  pair P0 (code_pf pf) (enc_form_nat target).

Definition check_code (p u : nat) : Prop :=
  exists pf target,
    p = code_pf pf /\
    u = code_of_concrete pf target /\
    check pf target = true.

Lemma check_code_unfold :
  forall p u,
    check_code p u <->
    exists pf target,
      p = code_pf pf /\
      u = code_of_concrete pf target /\
      check pf target = true.
Proof.
  intros p u.
  unfold check_code.
  tauto.
Qed.

Definition CubicSolvableCodeConcrete
  (pf : Proof) (target : Form) (n : nat) : Prop :=
  n = code_of_concrete pf target /\ CubicSatObj pf target.

Theorem check_iff_cubic_code_concrete :
  forall pf target,
    check pf target = true <->
    CubicSolvableCodeConcrete pf target (code_of_concrete pf target).
Proof.
  intros pf target.
  split.
  - intros Hcheck.
    split.
    + reflexivity.
    + apply (proj1 (check_iff_cubic_sat_obj pf target)).
      exact Hcheck.
  - intros [_ Hsat].
    apply (proj2 (check_iff_cubic_sat_obj pf target)).
    exact Hsat.
Qed.