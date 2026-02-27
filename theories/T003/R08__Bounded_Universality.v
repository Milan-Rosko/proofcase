(* R08__Bounded_Universality.v *)

From Coq Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

From T003 Require Import R00__VarMap R01__Coeff_types R04__Universal R07__Table_Inspection.

Definition InputEncoding_table (t : nat) (rho : env) : Prop :=
  rho (uc_ix_u UC) = Z.of_nat t.

Definition RepresentationBound (rho : env) : Prop :=
  forall i, (i < var_count)%nat -> 0 <= rho i <= Z.of_nat bound_max_repr_full.

Definition Bounded_Thm_k (t : nat) : Prop :=
  exists rho : env,
    InputEncoding_table t rho /\
    RepresentationBound rho /\
    uc_U UC rho = 0.

Theorem bounded_universal_cubic :
  forall t,
    Bounded_Thm_k t <->
    exists rho : env,
      InputEncoding_table t rho /\
      RepresentationBound rho /\
      U_table rho = 0.
Proof.
  intro t.
  unfold Bounded_Thm_k.
  assert (Huc : forall rho, uc_U UC rho = U_table rho).
  { intro rho. reflexivity. }
  split; intros [rho [Hin [Hbd Hu]]].
  - exists rho.
    split; [exact Hin|].
    split; [exact Hbd|].
    rewrite <- Huc.
    exact Hu.
  - exists rho.
    split; [exact Hin|].
    split; [exact Hbd|].
    rewrite Huc.
    exact Hu.
Qed.

Theorem bounded_endpoint_inspects_table :
  table_digest_of (uc_poly UC) = table_digest_expected.
Proof.
  exact (uc_digest_ok UC).
Qed.

Theorem bounded_universal_cubic_endpoint :
  forall t,
    table_digest_of (uc_poly UC) = table_digest_expected /\
    (Bounded_Thm_k t <->
      exists rho : env,
        InputEncoding_table t rho /\
        RepresentationBound rho /\
        U_table rho = 0).
Proof.
  intro t.
  split.
  - exact bounded_endpoint_inspects_table.
  - exact (bounded_universal_cubic t).
Qed.

Print Assumptions bounded_universal_cubic.
Print Assumptions bounded_endpoint_inspects_table.
Print Assumptions bounded_universal_cubic_endpoint.
