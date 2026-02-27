(* P01__HBL.v *)

From Coq Require Import List Bool.
Import ListNotations.

From T002 Require Import P00__Concrete_Provability.
From T002 Require Import P02__Diagonal.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R06__Encoding_Formula_Coding
  R15__Code_Bridge.

Definition ProvCodeConcrete (u : nat) : Prop :=
  ProvCode u.

Theorem Prov_sigma1 :
  forall u, ProvCodeConcrete u <-> exists p, Concrete_Proof p u.
Proof.
  intros u.
  unfold ProvCodeConcrete, ProvCode.
  tauto.
Qed.

Theorem Prov_from_check :
  forall pf target,
    check pf target = true ->
    ProvCodeConcrete (code_of_concrete pf target).
Proof.
  intros pf target Hcheck.
  unfold ProvCodeConcrete.
  apply checker_accepts_implies_ProvCode.
  exact Hcheck.
Qed.

Theorem Prov_to_concrete_witness :
  forall u,
    ProvCodeConcrete u ->
    exists p, Concrete_Proof p u.
Proof.
  intros u Hu.
  apply (proj1 (Prov_sigma1 u)).
  exact Hu.
Qed.

Theorem HBL_1 :
  forall pf target,
    check pf target = true ->
    ProvCodeConcrete (code_of_concrete pf target).
Proof.
  intros pf target Hcheck.
  apply Prov_from_check.
  exact Hcheck.
Qed.

Theorem HBL_2 :
  forall u,
    ProvCodeConcrete u ->
    exists p, Concrete_Proof p u.
Proof.
  intros u Hu.
  apply Prov_to_concrete_witness.
  exact Hu.
Qed.

Lemma existsb_local_complete :
  forall (A : Type) (p : A -> bool) (xs : list A),
    (exists x, In x xs /\ p x = true) ->
    existsb_local p xs = true.
Proof.
  intros A p xs.
  induction xs as [|x xs IH]; intros [y [Hin Hy]].
  - inversion Hin.
  - simpl in Hin.
    simpl.
    destruct Hin as [Heq|Hin].
    + subst y. rewrite Hy. reflexivity.
    + destruct (p x) eqn:Hx.
      * reflexivity.
      * apply IH.
        exists y. split; assumption.
Qed.

Lemma mp_witness_from_in :
  forall (ctx : list Form) (u v : Form),
    In u ctx ->
    In (Imp u v) ctx ->
    mp_witness ctx v = true.
Proof.
  intros ctx u v Hu Himp.
  unfold mp_witness.
  apply existsb_local_complete.
  exists u.
  split; [exact Hu|].
  apply existsb_local_complete.
  exists (Imp u v).
  split; [exact Himp|].
  simpl.
  rewrite form_eqb_refl, form_eqb_refl.
  reflexivity.
Qed.

Lemma mp_witness_monotone_incl :
  forall (ctx1 ctx2 : list Form) (phi : Form),
    (forall x, In x ctx1 -> In x ctx2) ->
    mp_witness ctx1 phi = true ->
    mp_witness ctx2 phi = true.
Proof.
  intros ctx1 ctx2 phi Hincl Hmp.
  unfold mp_witness in *.
  apply existsb_local_sound in Hmp.
  destruct Hmp as [psi [Hpsi Hinner]].
  apply existsb_local_sound in Hinner.
  destruct Hinner as [chi [Hchi Htest]].
  apply existsb_local_complete.
  exists psi.
  split.
  - apply Hincl. exact Hpsi.
  - apply existsb_local_complete.
    exists chi.
    split.
    + apply Hincl. exact Hchi.
    + exact Htest.
Qed.

Lemma check_lines_monotone_incl :
  forall (ctx1 ctx2 : list Form) (pf : Proof),
    (forall x, In x ctx1 -> In x ctx2) ->
    check_lines ctx1 pf = true ->
    check_lines ctx2 pf = true.
Proof.
  intros ctx1 ctx2 pf Hincl.
  revert ctx1 ctx2 Hincl.
  induction pf as [|line rest IH]; intros ctx1 ctx2 Hincl Hcheck.
  - reflexivity.
  - simpl in Hcheck.
    apply Bool.andb_true_iff in Hcheck as [Hok Hrest].
    simpl.
    apply Bool.andb_true_iff.
    split.
    + apply Bool.orb_true_iff in Hok as [Hax|Hmp].
      * apply Bool.orb_true_iff. left. exact Hax.
      * apply Bool.orb_true_iff. right.
        apply (mp_witness_monotone_incl ctx1 ctx2 line Hincl Hmp).
    + apply (IH (line :: ctx1) (line :: ctx2)).
      * intros x Hx.
        simpl in Hx.
        simpl.
        destruct Hx as [Hx|Hx].
        -- left. exact Hx.
        -- right. apply Hincl. exact Hx.
      * exact Hrest.
Qed.

Lemma check_lines_consume_rev :
  forall (ctx : list Form) (pf : Proof),
    check_lines ctx pf = true ->
    check_lines (rev pf ++ ctx) [] = true.
Proof.
  intros ctx pf H.
  simpl.
  reflexivity.
Qed.

Lemma check_lines_cat :
  forall (ctx : list Form) (pf1 pf2 : Proof),
    check_lines ctx pf1 = true ->
    check_lines (rev pf1 ++ ctx) pf2 = true ->
    check_lines ctx (pf1 ++ pf2) = true.
Proof.
  intros ctx pf1.
  revert ctx.
  induction pf1 as [|a pf1 IH]; intros ctx pf2 H1 H2.
  - simpl in *. exact H2.
  - simpl in H1.
    apply Bool.andb_true_iff in H1 as [Ha Hrest].
    simpl.
    apply Bool.andb_true_iff.
    split; [exact Ha|].
    apply (IH (a :: ctx) pf2 Hrest).
    simpl in H2.
    rewrite <- app_assoc in H2.
    exact H2.
Qed.

Lemma last_opt_in :
  forall (pf : Proof) (last : Form),
    last_opt pf = Some last ->
    In last pf.
Proof.
  induction pf as [|x xs IH]; intros last Hlast.
  - discriminate.
  - destruct xs as [|y ys].
    + simpl in Hlast. inversion Hlast; subst. simpl. left. reflexivity.
    + simpl in Hlast. right. apply IH. exact Hlast.
Qed.

Lemma last_opt_app_singleton :
  forall (pf : Proof) (x : Form),
    last_opt (pf ++ [x]) = Some x.
Proof.
  induction pf as [|a pf IH]; intro x.
  - simpl. reflexivity.
  - simpl.
    destruct pf as [|b pf'].
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.

Lemma check_true_components :
  forall (pf : Proof) (goal : Form),
    check pf goal = true ->
    check_lines [] pf = true /\ last_opt pf = Some goal.
Proof.
  intros pf goal Hcheck.
  unfold check in Hcheck.
  destruct (last_opt pf) as [last|] eqn:Hlast; try discriminate.
  apply Bool.andb_true_iff in Hcheck as [Hlines Heq].
  apply form_eqb_true_eq in Heq.
  subst last.
  split.
  - exact Hlines.
  - reflexivity.
Qed.

(* Concrete MP internalization for checker-accepted proof traces. *)
Theorem Prov_MP_checker :
  forall (u v : Form) (pf_u pf_imp : Proof),
    check pf_u u = true ->
    check pf_imp (Imp u v) = true ->
    exists pf_v,
      check pf_v v = true /\
      ProvCodeConcrete (code_of_concrete pf_v v).
Proof.
  intros u v pf_u pf_imp Hu Himp.
  destruct (check_true_components pf_u u Hu) as [Hlines_u Hlast_u].
  destruct (check_true_components pf_imp (Imp u v) Himp) as [Hlines_imp Hlast_imp].

  set (pf_v := pf_u ++ pf_imp ++ [v]).
  exists pf_v.
  assert (Hcheck_v : check pf_v v = true).
  {
    unfold pf_v.
    assert (Hlines_uimp : check_lines [] (pf_u ++ pf_imp) = true).
    {
      apply (check_lines_cat [] pf_u pf_imp).
      - exact Hlines_u.
      - rewrite app_nil_r.
        apply (check_lines_monotone_incl [] (rev pf_u)).
        + intros x Hx. inversion Hx.
        + exact Hlines_imp.
    }

    assert (Hin_u_ctx : In u (rev pf_imp ++ rev pf_u)).
    {
      apply in_or_app.
      right.
      apply (proj1 (in_rev pf_u u)).
      apply last_opt_in with (pf := pf_u).
      exact Hlast_u.
    }

    assert (Hin_imp_ctx : In (Imp u v) (rev pf_imp ++ rev pf_u)).
    {
      apply in_or_app.
      left.
      apply (proj1 (in_rev pf_imp (Imp u v))).
      apply last_opt_in with (pf := pf_imp).
      exact Hlast_imp.
    }

    assert (Hlines_v : check_lines (rev (pf_u ++ pf_imp)) [v] = true).
    {
      rewrite rev_app_distr.
      simpl.
      apply Bool.andb_true_iff.
      split.
      - apply Bool.orb_true_iff. right.
        eapply mp_witness_from_in.
        + exact Hin_u_ctx.
        + exact Hin_imp_ctx.
      - reflexivity.
    }

    assert (Hlines_total : check_lines [] ((pf_u ++ pf_imp) ++ [v]) = true).
    {
      apply (check_lines_cat [] (pf_u ++ pf_imp) [v]).
      - exact Hlines_uimp.
      - rewrite app_nil_r.
        exact Hlines_v.
    }

    unfold check.
    rewrite app_assoc.
    rewrite last_opt_app_singleton.
    rewrite Hlines_total.
    rewrite form_eqb_refl.
    reflexivity.
  }
  split.
  - exact Hcheck_v.
  - unfold ProvCodeConcrete.
    apply checker_accepts_implies_ProvCode.
    exact Hcheck_v.
Qed.

Definition ProvFormula (phi : Form) : Prop :=
  exists pf, check pf phi = true.

Theorem Prov_MP :
  forall (u v : Form),
    ProvFormula (Imp u v) ->
    ProvFormula u ->
    ProvFormula v.
Proof.
  intros u v [pf_imp Himp] [pf_u Hu].
  destruct (Prov_MP_checker u v pf_u pf_imp Hu Himp) as [pf_v [Hcheck _]].
  exists pf_v.
  exact Hcheck.
Qed.

Theorem HBL_3 :
  forall (u v : Form),
    ProvFormula (Imp u v) ->
    ProvFormula u ->
    ProvFormula v.
Proof.
  intros u v Himp Hu.
  apply (Prov_MP u v Himp Hu).
Qed.

Theorem Prov_subst :
  forall hole_code A t,
    (forall a b, unpair P0 (pair P0 a b) = (a, b)) ->
    hole_code <> 0 ->
    (forall a b, hole_code <> S (pair P0 a b)) ->
    ClosedCode t ->
    ClosedCode
      (apply_oform hole_code A t).
Proof.
  intros hole_code A t Hup Hbot Hfresh Hclosed.
  apply (apply_oform_closed hole_code Hup Hbot Hfresh A t).
  exact Hclosed.
Qed.

Definition code_map_represents (F : nat -> nat) : Prop :=
  forall t, ClosedCode t -> ClosedCode (F t).

Theorem Prov_representation :
  forall hole_code A,
    (forall a b, unpair P0 (pair P0 a b) = (a, b)) ->
    hole_code <> 0 ->
    (forall a b, hole_code <> S (pair P0 a b)) ->
    code_map_represents (apply_oform hole_code A).
Proof.
  intros hole_code A Hup Hbot Hfresh t Hclosed.
  apply (Prov_subst hole_code A t Hup Hbot Hfresh).
  exact Hclosed.
Qed.