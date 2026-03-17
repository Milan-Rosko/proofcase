(* R02__Phase_Two.v *)

From Coq Require Import Arith Bool Classical Lia List ZArith.
Import ListNotations.

From T004 Require Import R01__Phase_One.

Open Scope Z_scope.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 Phase 2                                          *)
(*                                                                       *)
(*  Consolidated Phase 2 theory unit.                                    *)
(*                                                                       *)
(*  Phase 2 is the constructive cutoff-memory layer of T004.  Its        *)
(*  central question is: if a bounded predecessor row already realizes   *)
(*  the seed window on [-R, R], what forced asymmetry remains visible    *)
(*  in that row?                                                         *)
(*                                                                       *)
(*  The file has three main strands.                                     *)
(*                                                                       *)
(*    1. Local seed-window realization and outer-shell emission.         *)
(*                                                                       *)
(*       Bounded realization of the seed window cannot remain confined   *)
(*       to a too-small support; it must emit visible shell data.        *)
(*                                                                       *)
(*    2. Recursive left/right pressure transport.                        *)
(*                                                                       *)
(*       The shell equations force either persistent far-left pressure   *)
(*       or repeated right-side compactification inward, until left      *)
(*       memory is recovered.                                            *)
(*                                                                       *)
(*    3. Phase 2 endpoint and auxiliary reverse vocabulary.              *)
(*                                                                       *)
(*       The endpoint original_sin_theorem packages this left-memory     *)
(*       residue as a bounded certificate.  The later auxiliary objects  *)
(*       expose seeded-prefix and glitchprojection language used by the  *)
(*       reverse-side finite analysis.                                   *)
(*                                                                       *)
(*************************************************************************)

Section Glitch_Compactness.

Inductive glitch_side : Type :=
| glitch_left
| glitch_right.

Record glitch_site : Type := {
  gs_side : glitch_side;
  gs_time : nat;
  gs_center : Z
}.

Definition replay_window (u : space_time) (n t : nat) : list bit :=
  window_data u n t.

Definition agrees_on (L U : Z) (u v : row) : Prop :=
  forall x,
    (L <= x <= U)%Z ->
    u x = v x.

Definition local_seed_window_realization (R : nat) (u : row) : Prop :=
  forall x,
    (Z.abs x <= Z.of_nat R)%Z ->
    step u x = seed_row x.

Definition truncate (N : nat) (u : row) : row :=
  fun x =>
    if Z.leb (- Z.of_nat N) x && Z.leb x (Z.of_nat N)
    then u x
    else false.

(*
  The compact center trap already visible inside “the Fall.”

  A seed-creation triplet is the local 3-cell configuration that forces a
  center output of true from two leading zeros.  Once the successor output is
  also required to be false, contradiction is immediate and no far-away data
  matters anymore.
*)

Definition seed_creation_triplet (r : row) (c : Z) : Prop :=
  r (c - 1)%Z = false /\
  r c = false /\
  step r c = true.

Definition compact_fall_trap (r : row) (c : Z) : Prop :=
  seed_creation_triplet r c /\
  step r (c + 1)%Z = false.

Lemma seed_creation_triplet_forces_right_true :
  forall r c,
    seed_creation_triplet r c ->
    r (c + 1)%Z = true.
Proof.
  intros r c [Hleft [Hmid Hstep]].
  unfold step, step_row in Hstep.
  rewrite Hleft, Hmid in Hstep.
  exact Hstep.
Qed.

Lemma compact_fall_trap_impossible :
  forall r c,
    compact_fall_trap r c ->
    False.
Proof.
  intros r c [[Hleft [Hmid Hstepc]] Hstepnext].
  pose proof (seed_creation_triplet_forces_right_true r c (conj Hleft (conj Hmid Hstepc)))
    as Hright.
  unfold step, step_row in Hstepnext.
  replace ((c + 1) - 1)%Z with c in Hstepnext by lia.
  replace ((c + 1) + 1)%Z with (c + 2)%Z in Hstepnext by lia.
  rewrite Hmid, Hright in Hstepnext.
  simpl in Hstepnext.
  discriminate.
Qed.

Lemma step_local :
  forall u v x,
    agrees_on (x - 1) (x + 1) u v ->
    step u x = step v x.
Proof.
  intros u v x Hagree.
  unfold step, step_row.
  assert (Hleft : u (x - 1)%Z = v (x - 1)%Z).
  {
    apply Hagree.
    lia.
  }
  assert (Hmid : u x = v x).
  {
    apply Hagree.
    lia.
  }
  assert (Hright : u (x + 1)%Z = v (x + 1)%Z).
  {
    apply Hagree.
    lia.
  }
  rewrite Hleft, Hmid, Hright.
  reflexivity.
Qed.

Lemma step_local_window :
  forall R u v,
    agrees_on (- Z.of_nat R - 1) (Z.of_nat R + 1) u v ->
    forall x,
      (Z.abs x <= Z.of_nat R)%Z ->
      step u x = step v x.
Proof.
  intros R u v Hagree x Hx.
  apply step_local.
  intros y Hy.
  apply Hagree.
  destruct (Zabs_spec x) as [[Hnonneg Hxeq] | [Hneg Hxeq]];
  rewrite Hxeq in Hx;
  lia.
Qed.

Lemma local_seed_window_realization_ext :
  forall R u v,
    agrees_on (- Z.of_nat R - 1) (Z.of_nat R + 1) u v ->
    (local_seed_window_realization R u <->
     local_seed_window_realization R v).
Proof.
  intros R u v Hagree.
  split; intros Hreal x Hx.
  - rewrite <- (step_local_window R u v Hagree x Hx).
    apply Hreal.
    exact Hx.
  - rewrite (step_local_window R u v Hagree x Hx).
    apply Hreal.
    exact Hx.
Qed.

Lemma local_seed_window_realization_monotone :
  forall R S u,
    (R <= S)%nat ->
    local_seed_window_realization S u ->
    local_seed_window_realization R u.
Proof.
  intros R S u HRS Hreal x Hx.
  apply Hreal.
  lia.
Qed.

Lemma truncate_agrees :
  forall R N u,
    (R + 1 <= N)%nat ->
    agrees_on (- Z.of_nat R - 1) (Z.of_nat R + 1) (truncate N u) u.
Proof.
  intros R N u HN x Hx.
  unfold truncate.
  assert (Hlb : (- Z.of_nat N <= x)%Z) by lia.
  assert (Hub : (x <= Z.of_nat N)%Z) by lia.
  assert (Hlb_bool : Z.leb (- Z.of_nat N) x = true).
  {
    apply Z.leb_le.
    exact Hlb.
  }
  assert (Hub_bool : Z.leb x (Z.of_nat N) = true).
  {
    apply Z.leb_le.
    exact Hub.
  }
  rewrite Hlb_bool, Hub_bool.
  reflexivity.
Qed.

Lemma local_seed_window_realization_truncate :
  forall R N u,
    (R + 1 <= N)%nat ->
    local_seed_window_realization R u ->
    local_seed_window_realization R (truncate N u).
Proof.
  intros R N u HN Hreal.
  apply (proj2
    (local_seed_window_realization_ext R (truncate N u) u
      (truncate_agrees R N u HN))).
  exact Hreal.
Qed.

Lemma truncate_outside_radius :
  forall N u x,
    (Z.of_nat N < Z.abs x)%Z ->
    truncate N u x = false.
Proof.
  intros N u x Hout.
  unfold truncate.
  destruct (Z.leb (- Z.of_nat N) x && Z.leb x (Z.of_nat N)) eqn:Hinside.
  - apply andb_true_iff in Hinside.
    destruct Hinside as [Hlb Hub].
    apply Z.leb_le in Hlb.
    apply Z.leb_le in Hub.
    destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
      rewrite Habs in Hout;
      lia.
  - reflexivity.
Qed.

Lemma truncate_inside_radius :
  forall N u x,
    (Z.abs x <= Z.of_nat N)%Z ->
    truncate N u x = u x.
Proof.
  intros N u x Hin.
  unfold truncate.
  assert (Hlb : (- Z.of_nat N <= x)%Z) by lia.
  assert (Hub : (x <= Z.of_nat N)%Z) by lia.
  assert (Hlb_bool : Z.leb (- Z.of_nat N) x = true).
  {
    apply Z.leb_le.
    exact Hlb.
  }
  assert (Hub_bool : Z.leb x (Z.of_nat N) = true).
  {
    apply Z.leb_le.
    exact Hub.
  }
  rewrite Hlb_bool, Hub_bool.
  reflexivity.
Qed.

Lemma step_false_outside_support :
  forall u N x,
    (forall y,
      (y < - Z.of_nat N \/ Z.of_nat N < y)%Z ->
      u y = false) ->
    (Z.of_nat (S N) < Z.abs x)%Z ->
    step u x = false.
Proof.
  intros u N x Hsupp Hout.
  unfold step, step_row, rule30.
  destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]].
  - rewrite Habs in Hout.
    assert (Hleft : u (x - 1)%Z = false).
    {
      apply Hsupp.
      right.
      lia.
    }
    assert (Hmid : u x = false).
    {
      apply Hsupp.
      right.
      lia.
    }
    assert (Hright : u (x + 1)%Z = false).
    {
      apply Hsupp.
      right.
      lia.
    }
    rewrite Hleft, Hmid, Hright.
    reflexivity.
  - rewrite Habs in Hout.
    assert (Hleft : u (x - 1)%Z = false).
    {
      apply Hsupp.
      left.
      lia.
    }
    assert (Hmid : u x = false).
    {
      apply Hsupp.
      left.
      lia.
    }
    assert (Hright : u (x + 1)%Z = false).
    {
      apply Hsupp.
      left.
      lia.
    }
    rewrite Hleft, Hmid, Hright.
    reflexivity.
Qed.

Theorem local_seed_window_realization_with_support_bound_impossible :
  forall R N u,
    (forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      u x = false) ->
    (S N <= R)%nat ->
    local_seed_window_realization R u ->
    False.
Proof.
  intros R N u Hsupp Hbound Hreal.
  assert (Hglobal : forall x, step u x = seed_row x).
  {
    intro x.
    destruct (Z_le_gt_dec (Z.abs x) (Z.of_nat R)) as [Hin | Hout].
    - exact (Hreal x Hin).
    - assert (Hstep_false : step u x = false).
      {
        apply (step_false_outside_support u N x Hsupp).
        apply Nat2Z.inj_le in Hbound.
        lia.
      }
      assert (Hseed_false : seed_row x = false).
      {
        apply seed_row_neq_zero.
        intro Hx.
        subst x.
        lia.
      }
      rewrite Hstep_false, Hseed_false.
      reflexivity.
  }
  apply the_fall.
  exists u.
  split.
  - exists N.
    exact Hsupp.
  - exact Hglobal.
Qed.

Theorem local_seed_window_realization_with_small_support_impossible :
  forall N u,
    (forall x,
      (x < - Z.of_nat N \/ Z.of_nat N < x)%Z ->
      u x = false) ->
    local_seed_window_realization (S N) u ->
    False.
Proof.
  intros N u Hsupp Hreal.
  apply (local_seed_window_realization_with_support_bound_impossible (S N) N u Hsupp).
  - lia.
  - exact Hreal.
Qed.

Lemma shell_coordinate_cases :
  forall N x,
    (Z.of_nat N < Z.abs x <= Z.of_nat (S (S N)))%Z ->
    x = (- Z.of_nat (S (S N)))%Z \/
    x = (- Z.of_nat (S N))%Z \/
    x = (Z.of_nat (S N))%Z \/
    x = (Z.of_nat (S (S N)))%Z.
Proof.
  intros N x Hshell.
  destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
    rewrite Habs in Hshell;
    lia.
Qed.

Inductive outer_shell_site : Type :=
| outer_far_left
| outer_left
| outer_right
| outer_far_right.

Definition outer_shell_coord (N : nat) (s : outer_shell_site) : Z :=
  match s with
  | outer_far_left => (- Z.of_nat (S (S N)))%Z
  | outer_left => (- Z.of_nat (S N))%Z
  | outer_right => (Z.of_nat (S N))%Z
  | outer_far_right => (Z.of_nat (S (S N)))%Z
  end.

Definition outer_shell_value (N : nat) (u : row) (s : outer_shell_site) : bit :=
  truncate (S (S N)) u (outer_shell_coord N s).

Definition outer_shell_nonempty (N : nat) (u : row) : Prop :=
  exists s, outer_shell_value N u s = true.

Definition outer_shell_signature (N : nat) (u : row) : list bit :=
  [ outer_shell_value N u outer_far_left;
    outer_shell_value N u outer_left;
    outer_shell_value N u outer_right;
    outer_shell_value N u outer_far_right ].

Theorem local_seed_window_realization_requires_outer_shell :
  forall N u,
    local_seed_window_realization (S N) u ->
    exists x,
      (Z.of_nat N < Z.abs x <= Z.of_nat (S (S N)))%Z /\
      truncate (S (S N)) u x = true.
Proof.
  intros N u Hreal.
  set (v := truncate (S (S N)) u).
  assert (Hreal_v : local_seed_window_realization (S N) v).
  {
    unfold v.
    apply (local_seed_window_realization_truncate (S N) (S (S N)) u).
    - lia.
    - exact Hreal.
  }
  destruct (v (- Z.of_nat (S (S N)))%Z) eqn:Hminus2.
  - exists (- Z.of_nat (S (S N)))%Z.
    split.
    + lia.
    + exact Hminus2.
  - destruct (v (- Z.of_nat (S N))%Z) eqn:Hminus1.
    + exists (- Z.of_nat (S N))%Z.
      split.
      * lia.
      * exact Hminus1.
    + destruct (v (Z.of_nat (S N))%Z) eqn:Hplus1.
      * exists (Z.of_nat (S N))%Z.
        split.
        -- lia.
        -- exact Hplus1.
      * destruct (v (Z.of_nat (S (S N)))%Z) eqn:Hplus2.
        -- exists (Z.of_nat (S (S N)))%Z.
           split.
           ++ lia.
           ++ exact Hplus2.
        -- exfalso.
           apply (local_seed_window_realization_with_small_support_impossible N v).
           ++ intros x Hx.
              destruct (Z_lt_le_dec (Z.of_nat (S (S N))) (Z.abs x)) as [Hfar | Hnear].
              ** unfold v.
                 exact (truncate_outside_radius (S (S N)) u x Hfar).
              ** assert (Hshell : (Z.of_nat N < Z.abs x <= Z.of_nat (S (S N)))%Z).
                 {
                   destruct Hx as [Hx | Hx];
                   destruct (Zabs_spec x) as [[Hnonneg Habs] | [Hneg Habs]];
                     rewrite Habs;
                     lia.
                 }
                 destruct (shell_coordinate_cases N x Hshell)
                   as [Hxeq | [Hxeq | [Hxeq | Hxeq]]].
                 --- rewrite Hxeq.
                     exact Hminus2.
                 --- rewrite Hxeq.
                     exact Hminus1.
                 --- rewrite Hxeq.
                     exact Hplus1.
                 --- rewrite Hxeq.
                     exact Hplus2.
           ++ exact Hreal_v.
Qed.

Theorem local_seed_window_realization_requires_outer_shell_nonempty :
  forall N u,
    local_seed_window_realization (S N) u ->
    outer_shell_nonempty N u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_requires_outer_shell N u Hreal)
    as [x [Hshell Hhit]].
  unfold outer_shell_nonempty, outer_shell_value, outer_shell_coord.
  destruct (shell_coordinate_cases N x Hshell)
    as [Hxeq | [Hxeq | [Hxeq | Hxeq]]].
  - exists outer_far_left.
    rewrite <- Hxeq.
    exact Hhit.
  - exists outer_left.
    rewrite <- Hxeq.
    exact Hhit.
  - exists outer_right.
    rewrite <- Hxeq.
    exact Hhit.
  - exists outer_far_right.
    rewrite <- Hxeq.
    exact Hhit.
Qed.

Theorem local_seed_window_realization_requires_nonzero_shell_signature :
  forall N u,
    local_seed_window_realization (S N) u ->
    outer_shell_signature N u <> [false; false; false; false].
Proof.
  intros N u Hreal Hsig.
  destruct (local_seed_window_realization_requires_outer_shell_nonempty N u Hreal)
    as [s Hvalue].
  unfold outer_shell_signature in Hsig.
  destruct s;
    inversion Hsig;
    rewrite Hvalue in *;
    discriminate.
Qed.

(*
  Obligation language on the finite shell.

  The shell bits are not meant as a configuration to enumerate exhaustively.
  They are a finite carrier for recursive XOR-obligations forced by the edge
  equations of Rule 30 under zero outer background.
*)

Inductive shell_obligation : Type :=
| obligation_left
| obligation_right
| obligation_bilateral.

Definition realizes_left_shell_obligation (N : nat) (u : row) : Prop :=
  outer_shell_value N u outer_far_left = true \/
  outer_shell_value N u outer_left = true.

Definition realizes_right_shell_obligation (N : nat) (u : row) : Prop :=
  outer_shell_value N u outer_right = true \/
  outer_shell_value N u outer_far_right = true.

Definition realizes_shell_obligation (N : nat) (u : row) (o : shell_obligation) : Prop :=
  match o with
  | obligation_left =>
      realizes_left_shell_obligation N u
  | obligation_right =>
      realizes_right_shell_obligation N u
  | obligation_bilateral =>
      realizes_left_shell_obligation N u /\
      realizes_right_shell_obligation N u
  end.

Theorem local_seed_window_realization_emits_shell_obligation :
  forall N u,
    local_seed_window_realization (S N) u ->
    realizes_shell_obligation N u obligation_left \/
    realizes_shell_obligation N u obligation_right.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_requires_outer_shell_nonempty N u Hreal)
    as [s Hvalue].
  destruct s.
  - left.
    left.
    exact Hvalue.
  - left.
    right.
    exact Hvalue.
  - right.
    left.
    exact Hvalue.
  - right.
    right.
    exact Hvalue.
Qed.

Definition right_edge_zero_equation (N : nat) (u : row) : Prop :=
  step (truncate (S (S N)) u) (Z.of_nat (S N)) = false.

Definition left_edge_zero_equation (N : nat) (u : row) : Prop :=
  step (truncate (S (S N)) u) (- Z.of_nat (S N)) = false.

Lemma right_edge_zero_equation_from_seed_window :
  forall N u,
    local_seed_window_realization (S N) u ->
    right_edge_zero_equation N u.
Proof.
  intros N u Hreal.
  unfold right_edge_zero_equation.
  pose proof (local_seed_window_realization_truncate (S N) (S (S N)) u) as Htrunc.
  specialize (Htrunc ltac:(lia) Hreal).
  specialize (Htrunc (Z.of_nat (S N))).
  assert (Habs : (Z.abs (Z.of_nat (S N)) <= Z.of_nat (S N))%Z) by lia.
  specialize (Htrunc Habs).
  assert (Hseed_false : seed_row (Z.of_nat (S N)) = false).
  {
    apply seed_row_neq_zero.
    lia.
  }
  rewrite Hseed_false in Htrunc.
  exact Htrunc.
Qed.

Lemma left_edge_zero_equation_from_seed_window :
  forall N u,
    local_seed_window_realization (S N) u ->
    left_edge_zero_equation N u.
Proof.
  intros N u Hreal.
  unfold left_edge_zero_equation.
  pose proof (local_seed_window_realization_truncate (S N) (S (S N)) u) as Htrunc.
  specialize (Htrunc ltac:(lia) Hreal).
  specialize (Htrunc (- Z.of_nat (S N))).
  assert (Habs : (Z.abs (- Z.of_nat (S N)) <= Z.of_nat (S N))%Z) by lia.
  specialize (Htrunc Habs).
  assert (Hseed_false : seed_row (- Z.of_nat (S N)) = false).
  {
    apply seed_row_neq_zero.
    lia.
  }
  rewrite Hseed_false in Htrunc.
  exact Htrunc.
Qed.

Lemma right_edge_zero_equation_unfolds_to_xor_obligation :
  forall N u,
    right_edge_zero_equation N u ->
    truncate (S (S N)) u (Z.of_nat N) =
      orb (outer_shell_value N u outer_right)
          (outer_shell_value N u outer_far_right).
Proof.
  intros N u Hzero.
  unfold right_edge_zero_equation, outer_shell_value, outer_shell_coord in *.
  unfold step, step_row, rule30 in Hzero.
  replace (Z.of_nat (S N) - 1)%Z with (Z.of_nat N)%Z in Hzero by lia.
  replace (Z.of_nat (S N) + 1)%Z with (Z.of_nat (S (S N)))%Z in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat N)) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat (S N))) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat (S (S N)))) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat N)) by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat (S N))) by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat (S (S N)))) by lia.
  set (a := u (Z.of_nat N)) in *.
  set (b := u (Z.of_nat (S N))) in *.
  set (c := u (Z.of_nat (S (S N)))) in *.
  destruct a, b, c;
  simpl in *;
  try discriminate;
  reflexivity.
Qed.

Lemma left_edge_zero_equation_unfolds_to_xor_obligation :
  forall N u,
    left_edge_zero_equation N u ->
    outer_shell_value N u outer_far_left =
      orb (outer_shell_value N u outer_left)
          (truncate (S (S N)) u (- Z.of_nat N)).
Proof.
  intros N u Hzero.
  unfold left_edge_zero_equation, outer_shell_value, outer_shell_coord in *.
  unfold step, step_row, rule30 in Hzero.
  replace ((- Z.of_nat (S N)) - 1)%Z with (- Z.of_nat (S (S N)))%Z in Hzero by lia.
  replace ((- Z.of_nat (S N)) + 1)%Z with (- Z.of_nat N)%Z in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat (S (S N)))) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat (S N))) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat N)) in Hzero by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat (S (S N)))) by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat (S N))) by lia.
  rewrite (truncate_inside_radius (S (S N)) u (- Z.of_nat N)) by lia.
  set (a := u (- Z.of_nat (S (S N)))) in *.
  set (b := u (- Z.of_nat (S N))) in *.
  set (c := u (- Z.of_nat N)) in *.
  destruct a, b, c;
  simpl in *;
  try discriminate;
  reflexivity.
Qed.

Definition far_left_hot (N : nat) (u : row) : Prop :=
  outer_shell_value N u outer_far_left = true.

Definition inner_right_hot (N : nat) (u : row) : Prop :=
  truncate (S (S N)) u (Z.of_nat N) = true.

Lemma left_shell_obligation_forces_far_left_hot :
  forall N u,
    left_edge_zero_equation N u ->
    realizes_left_shell_obligation N u ->
    far_left_hot N u.
Proof.
  intros N u Hzero Hleft.
  unfold far_left_hot, realizes_left_shell_obligation in *.
  destruct Hleft as [Hfar | Hnear].
  - exact Hfar.
  - rewrite (left_edge_zero_equation_unfolds_to_xor_obligation N u Hzero).
    rewrite Hnear.
    reflexivity.
Qed.

Lemma right_shell_obligation_forces_inner_right_hot :
  forall N u,
    right_edge_zero_equation N u ->
    realizes_right_shell_obligation N u ->
    inner_right_hot N u.
Proof.
  intros N u Hzero Hright.
  unfold inner_right_hot, realizes_right_shell_obligation in *.
  rewrite (right_edge_zero_equation_unfolds_to_xor_obligation N u Hzero).
  destruct Hright as [Hnear | Hfar].
  - rewrite Hnear.
    reflexivity.
  - rewrite Hfar.
    destruct (outer_shell_value N u outer_right);
      reflexivity.
Qed.

Theorem local_seed_window_realization_forces_far_left_or_inner_right :
  forall N u,
    local_seed_window_realization (S N) u ->
    far_left_hot N u \/ inner_right_hot N u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_emits_shell_obligation N u Hreal)
    as [Hleft | Hright].
  - left.
    apply (left_shell_obligation_forces_far_left_hot N u).
    + apply (left_edge_zero_equation_from_seed_window N u).
      exact Hreal.
    + exact Hleft.
  - right.
    apply (right_shell_obligation_forces_inner_right_hot N u).
    + apply (right_edge_zero_equation_from_seed_window N u).
      exact Hreal.
    + exact Hright.
Qed.

Lemma inner_right_hot_compactifies_to_smaller_right_obligation :
  forall N u,
    inner_right_hot (S N) u ->
    realizes_right_shell_obligation N u.
Proof.
  intros N u Hhot.
  unfold inner_right_hot, realizes_right_shell_obligation, outer_shell_value, outer_shell_coord in *.
  left.
  rewrite (truncate_inside_radius (S (S (S N))) u (Z.of_nat (S N))) in Hhot by lia.
  rewrite (truncate_inside_radius (S (S N)) u (Z.of_nat (S N))) by lia.
  exact Hhot.
Qed.

Theorem local_seed_window_realization_forces_left_persistence_or_right_compactification :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    far_left_hot (S N) u \/ realizes_right_shell_obligation N u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_forces_far_left_or_inner_right (S N) u Hreal)
    as [Hleft | Hright].
  - left.
    exact Hleft.
  - right.
    exact (inner_right_hot_compactifies_to_smaller_right_obligation N u Hright).
Qed.

Lemma right_shell_obligation_compactifies_one_step :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    realizes_right_shell_obligation (S N) u ->
    realizes_right_shell_obligation N u.
Proof.
  intros N u Hreal Hright.
  apply (inner_right_hot_compactifies_to_smaller_right_obligation N u).
  apply (right_shell_obligation_forces_inner_right_hot (S N) u).
  - apply (right_edge_zero_equation_from_seed_window (S N) u).
    exact Hreal.
  - exact Hright.
Qed.

Theorem right_shell_obligation_compactifies_to_smaller_radius :
  forall k m u,
    local_seed_window_realization (S (S (k + m))) u ->
    realizes_right_shell_obligation (k + m) u ->
    realizes_right_shell_obligation k u.
Proof.
  intros k m u Hreal Hright.
  revert k u Hreal Hright.
  induction m as [|m IH]; intros k u Hreal Hright.
  - replace (k + 0)%nat with k in * by lia.
    exact Hright.
  - replace (k + S m)%nat with (S (k + m)) in * by lia.
    assert (Hreal' : local_seed_window_realization (S (S (k + m))) u).
    {
      apply (local_seed_window_realization_monotone
        (S (S (k + m)))
        (S (S (S (k + m))))
        u).
      - lia.
      - exact Hreal.
    }
    assert (Hright' : realizes_right_shell_obligation (k + m) u).
    {
      apply (right_shell_obligation_compactifies_one_step (k + m) u).
      - exact Hreal'.
      - exact Hright.
    }
    exact (IH k u Hreal' Hright').
Qed.

Theorem local_seed_window_realization_either_left_persists_or_right_compactifies_to_core :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    far_left_hot (S N) u \/ realizes_right_shell_obligation 0 u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_forces_left_persistence_or_right_compactification N u Hreal)
    as [Hleft | Hright].
  - left.
    exact Hleft.
  - right.
    replace N with (0 + N)%nat in Hright by lia.
    exact (right_shell_obligation_compactifies_to_smaller_radius 0 N u Hreal Hright).
Qed.

Theorem local_seed_window_realization_without_left_persistence_compactifies_right_to_core :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    ~ far_left_hot (S N) u ->
    realizes_right_shell_obligation 0 u.
Proof.
  intros N u Hreal Hnleft.
  destruct (local_seed_window_realization_either_left_persists_or_right_compactifies_to_core N u Hreal)
    as [Hleft | Hcore].
  - contradiction.
  - exact Hcore.
Qed.

Lemma right_shell_obligation_at_core_forces_far_left_hot_one :
  forall u,
    local_seed_window_realization 2 u ->
    realizes_right_shell_obligation 0 u ->
    far_left_hot 1 u.
Proof.
  intros u Hreal2 Hright0.
  assert (Hreal1 : local_seed_window_realization 1 u).
  {
    apply (local_seed_window_realization_monotone 1 2 u).
    - lia.
    - exact Hreal2.
  }
  assert (Hzero0 : right_edge_zero_equation 0 u).
  {
    apply (right_edge_zero_equation_from_seed_window 0 u).
    exact Hreal1.
  }
  assert (Hinner0 : inner_right_hot 0 u).
  {
    apply (right_shell_obligation_forces_inner_right_hot 0 u Hzero0 Hright0).
  }
  assert (Hcenter : u 0 = true).
  {
    unfold inner_right_hot in Hinner0.
    change (truncate 2 u 0 = true) in Hinner0.
    rewrite (truncate_inside_radius 2 u 0) in Hinner0 by lia.
    exact Hinner0.
  }
  assert (Hleft_near : outer_shell_value 1 u outer_left = true).
  {
    assert (Hstepm1 : step u (-1) = false).
    {
      specialize (Hreal2 (-1)).
      assert (Habs : (Z.abs (-1) <= Z.of_nat 2)%Z) by lia.
      specialize (Hreal2 Habs).
      cbn in Hreal2.
      exact Hreal2.
    }
    unfold step, step_row, rule30 in Hstepm1.
    replace ((-1) - 1)%Z with (-2)%Z in Hstepm1 by lia.
    replace ((-1) + 1)%Z with 0%Z in Hstepm1 by lia.
    rewrite Hcenter in Hstepm1.
    assert (Hminus2 : u (-2)%Z = true).
    {
      destruct (u (-2)%Z) eqn:Hu2, (u (-1)%Z) eqn:Hu1;
        simpl in Hstepm1;
        try discriminate;
        reflexivity.
    }
    unfold outer_shell_value, outer_shell_coord.
    change (truncate 3 u (-2) = true).
    rewrite (truncate_inside_radius 3 u (-2)) by lia.
    exact Hminus2.
  }
  assert (Hzero_left1 : left_edge_zero_equation 1 u).
  {
    apply (left_edge_zero_equation_from_seed_window 1 u).
    exact Hreal2.
  }
  unfold far_left_hot.
  rewrite (left_edge_zero_equation_unfolds_to_xor_obligation 1 u Hzero_left1).
  rewrite Hleft_near.
  reflexivity.
Qed.

Theorem local_seed_window_realization_radius_two_forces_far_left_hot_one :
  forall u,
    local_seed_window_realization 2 u ->
    far_left_hot 1 u.
Proof.
  intros u Hreal2.
  destruct (local_seed_window_realization_forces_left_persistence_or_right_compactification 0 u Hreal2)
    as [Hleft1 | Hright0].
  - exact Hleft1.
  - exact (right_shell_obligation_at_core_forces_far_left_hot_one u Hreal2 Hright0).
Qed.

Definition bounded_right_avoidance_chain (N : nat) (u : row) : Prop :=
  local_seed_window_realization (S (S N)) u /\
  forall k,
    (k <= N)%nat ->
    ~ far_left_hot (S k) u.

Theorem bounded_right_avoidance_chain_impossible :
  forall N u,
    bounded_right_avoidance_chain N u ->
    False.
Proof.
  intros N u [Hreal Havoid].
  assert (Hright0 : realizes_right_shell_obligation 0 u).
  {
    apply (local_seed_window_realization_without_left_persistence_compactifies_right_to_core N u Hreal).
    apply (Havoid N).
    lia.
  }
  assert (Hreal2 : local_seed_window_realization 2 u).
  {
    apply (local_seed_window_realization_monotone 2 (S (S N)) u).
    - lia.
    - exact Hreal.
  }
  pose proof (right_shell_obligation_at_core_forces_far_left_hot_one u Hreal2 Hright0)
    as Hleft1.
  apply (Havoid 0%nat).
  - lia.
  - exact Hleft1.
Qed.

Lemma far_left_hot_decidable :
  forall N u,
    {far_left_hot N u} + {~ far_left_hot N u}.
Proof.
  intros N u.
  unfold far_left_hot.
  destruct (outer_shell_value N u outer_far_left) eqn:Hbit.
  - left.
    reflexivity.
  - right.
    intro Hhot.
    discriminate.
Qed.

Lemma find_far_left_hot_level_or_uniform_avoidance :
  forall N u,
    {k : nat | (k <= N)%nat /\ far_left_hot (S k) u} +
    {forall k,
        (k <= N)%nat ->
        ~ far_left_hot (S k) u}.
Proof.
  induction N as [|N IH]; intro u.
  - destruct (far_left_hot_decidable 1 u) as [Hhot | Hnot].
    + left.
      exists 0%nat.
      split.
      * lia.
      * exact Hhot.
    + right.
      intros k Hk.
      assert (k = 0%nat) by lia.
      subst k.
      exact Hnot.
  - destruct (IH u) as [[k [Hk Hhot]] | Hall].
    + left.
      exists k.
      split.
      * lia.
      * exact Hhot.
    + destruct (far_left_hot_decidable (S (S N)) u) as [Hhot | Hnot].
      * left.
        exists (S N).
        split.
        -- lia.
        -- exact Hhot.
      * right.
        intros k Hk.
        destruct (Nat.eq_dec k (S N)) as [Heq | Hneq].
        -- subst k.
           exact Hnot.
        -- apply Hall.
           lia.
Qed.

Theorem local_seed_window_realization_forces_left_persistence_level :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    {k : nat | (k <= N)%nat /\ far_left_hot (S k) u}.
Proof.
  intros N u Hreal.
  destruct (find_far_left_hot_level_or_uniform_avoidance N u) as [Hsome | Hall].
  - exact Hsome.
  - destruct (bounded_right_avoidance_chain_impossible N u).
    split.
    + exact Hreal.
    + exact Hall.
Qed.

Corollary local_seed_window_realization_forces_left_persistence_somewhere :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    exists k,
      (k <= N)%nat /\ far_left_hot (S k) u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_forces_left_persistence_level N u Hreal)
    as [k [Hk Hhot]].
  exists k.
  split.
  - exact Hk.
  - exact Hhot.
Qed.

Definition bounded_left_obligation_site (N : nat) : Type :=
  { k : nat | (k <= N)%nat }.

Definition bounded_left_obligation_level
    {N : nat} (s : bounded_left_obligation_site N) : nat :=
  proj1_sig s.

Definition bounded_left_obligation_at
    (N : nat) (u : row) (s : bounded_left_obligation_site N) : Prop :=
  far_left_hot (S (bounded_left_obligation_level s)) u.

Definition bounded_left_obligation_coord
    {N : nat} (s : bounded_left_obligation_site N) : Z :=
  (- Z.of_nat (bounded_left_obligation_level s + 3))%Z.

Record bounded_obligation_replay (N : nat) (u : row) : Type := {
  bor_realization :
    local_seed_window_realization (S (S N)) u;
  bor_site : bounded_left_obligation_site N;
  bor_obligation :
    bounded_left_obligation_at N u bor_site
}.

Theorem local_seed_window_realization_builds_bounded_obligation_replay :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    bounded_obligation_replay N u.
Proof.
  intros N u Hreal.
  destruct (local_seed_window_realization_forces_left_persistence_level N u Hreal)
    as [k [Hk Hhot]].
  refine
    {| bor_realization := Hreal;
       bor_site := exist _ k Hk;
       bor_obligation := _ |}.
  exact Hhot.
Defined.

Lemma bounded_left_obligation_at_unfolds_to_coordinate :
  forall N u (s : bounded_left_obligation_site N),
    bounded_left_obligation_at N u s ->
    u (bounded_left_obligation_coord s) = true.
Proof.
  intros N u [k Hk] Hob.
  simpl in *.
  unfold bounded_left_obligation_at, bounded_left_obligation_level in Hob.
  unfold far_left_hot, outer_shell_value, outer_shell_coord in Hob.
  change (truncate (S (S (S k))) u (- Z.of_nat (S (S (S k)))) = true) in Hob.
  rewrite (truncate_inside_radius (S (S (S k))) u (- Z.of_nat (S (S (S k))))) in Hob by lia.
  replace (bounded_left_obligation_coord (exist (fun k : nat => (k <= N)%nat) k Hk))
    with (- Z.of_nat (S (S (S k))))%Z.
  - exact Hob.
  - unfold bounded_left_obligation_coord, bounded_left_obligation_level.
    simpl.
    lia.
Qed.

Theorem bounded_obligation_replay_forces_left_hot_coordinate :
  forall N u,
    bounded_obligation_replay N u ->
    exists x,
      (- Z.of_nat (N + 3) <= x <= -3)%Z /\
      u x = true.
Proof.
  intros N u B.
  exists (bounded_left_obligation_coord (bor_site N u B)).
  split.
  - unfold bounded_left_obligation_coord, bounded_left_obligation_level.
    destruct (bor_site N u B) as [k Hk].
    simpl.
    lia.
  - apply (bounded_left_obligation_at_unfolds_to_coordinate N u (bor_site N u B)).
    exact (bor_obligation N u B).
Qed.

Theorem local_seed_window_realization_forces_left_hot_coordinate :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    exists x,
      (- Z.of_nat (N + 3) <= x <= -3)%Z /\
      u x = true.
Proof.
  intros N u Hreal.
  apply bounded_obligation_replay_forces_left_hot_coordinate.
  exact (local_seed_window_realization_builds_bounded_obligation_replay N u Hreal).
Qed.

Record bounded_left_obligation_chain (N : nat) (u : row) : Type := {
  bloc_realization :
    local_seed_window_realization (S (S N)) u;
  bloc_site :
    forall k,
      (k <= N)%nat ->
      bounded_left_obligation_site k;
  bloc_obligation :
    forall k (Hk : (k <= N)%nat),
      bounded_left_obligation_at k u (bloc_site k Hk)
}.

Theorem local_seed_window_realization_builds_bounded_left_obligation_chain :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    bounded_left_obligation_chain N u.
Proof.
  intros N u Hreal.
  refine
    {| bloc_realization := Hreal;
       bloc_site := fun k Hk =>
         bor_site k u
           (local_seed_window_realization_builds_bounded_obligation_replay
             k u
             (local_seed_window_realization_monotone
               (S (S k))
               (S (S N))
               u
               ltac:(lia)
               Hreal));
       bloc_obligation := _ |}.
  intros k Hk.
  exact
    (bor_obligation k u
      (local_seed_window_realization_builds_bounded_obligation_replay
        k u
        (local_seed_window_realization_monotone
          (S (S k))
          (S (S N))
          u
          ltac:(lia)
          Hreal))).
Defined.

Theorem bounded_left_obligation_chain_forces_coordinate_at_level :
  forall N u (C : bounded_left_obligation_chain N u) k (Hk : (k <= N)%nat),
    exists x,
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true.
Proof.
  intros N u C k Hk.
  exists (bounded_left_obligation_coord (bloc_site N u C k Hk)).
  split.
  - unfold bounded_left_obligation_coord, bounded_left_obligation_level.
    destruct (bloc_site N u C k Hk) as [j Hj].
    simpl.
    lia.
  - apply (bounded_left_obligation_at_unfolds_to_coordinate
      k u (bloc_site N u C k Hk)).
    exact (bloc_obligation N u C k Hk).
Qed.

Theorem bounded_left_obligation_chain_forces_coordinate_at_level_sig :
  forall N u (C : bounded_left_obligation_chain N u) k (Hk : (k <= N)%nat),
    { x : Z |
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true }.
Proof.
  intros N u C k Hk.
  exists (bounded_left_obligation_coord (bloc_site N u C k Hk)).
  split.
  - unfold bounded_left_obligation_coord, bounded_left_obligation_level.
    destruct (bloc_site N u C k Hk) as [j Hj].
    simpl.
    lia.
  - apply (bounded_left_obligation_at_unfolds_to_coordinate
      k u (bloc_site N u C k Hk)).
    exact (bloc_obligation N u C k Hk).
Defined.

Theorem local_seed_window_realization_forces_left_hot_coordinate_at_each_level :
  forall N u k,
    (k <= N)%nat ->
    local_seed_window_realization (S (S N)) u ->
    exists x,
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true.
Proof.
  intros N u k Hk Hreal.
  apply (bounded_left_obligation_chain_forces_coordinate_at_level
    N u
    (local_seed_window_realization_builds_bounded_left_obligation_chain N u Hreal)
    k
    Hk).
Qed.

Theorem local_seed_window_realization_forces_left_hot_coordinate_at_each_level_sig :
  forall N u k,
    (k <= N)%nat ->
    local_seed_window_realization (S (S N)) u ->
    { x : Z |
      (- Z.of_nat (k + 3) <= x <= -3)%Z /\
      u x = true }.
Proof.
  intros N u k Hk Hreal.
  exact
    (bounded_left_obligation_chain_forces_coordinate_at_level_sig
      N u
      (local_seed_window_realization_builds_bounded_left_obligation_chain N u Hreal)
      k
      Hk).
Defined.

Record bounded_left_coordinate_family (N : nat) (u : row) : Type := {
  blcf_coord :
    forall k,
      (k <= N)%nat ->
      Z;
  blcf_bounds :
    forall k (Hk : (k <= N)%nat),
      (- Z.of_nat (k + 3) <= blcf_coord k Hk <= -3)%Z;
  blcf_hot :
    forall k (Hk : (k <= N)%nat),
      u (blcf_coord k Hk) = true
}.

Theorem local_seed_window_realization_builds_bounded_left_coordinate_family :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    bounded_left_coordinate_family N u.
Proof.
  intros N u Hreal.
  refine
    {| blcf_coord := fun k Hk =>
         proj1_sig
           (local_seed_window_realization_forces_left_hot_coordinate_at_each_level_sig
             N u k Hk Hreal);
       blcf_bounds := _;
       blcf_hot := _ |}.
  - intros k Hk.
    exact
      (proj1 (proj2_sig
        (local_seed_window_realization_forces_left_hot_coordinate_at_each_level_sig
          N u k Hk Hreal))).
  - intros k Hk.
    exact
      (proj2 (proj2_sig
        (local_seed_window_realization_forces_left_hot_coordinate_at_each_level_sig
          N u k Hk Hreal))).
Defined.

Definition left_cold_slab (N : nat) (u : row) : Prop :=
  forall x,
    (- Z.of_nat (N + 3) <= x <= -3)%Z ->
    u x = false.

Theorem bounded_left_coordinate_family_implies_left_slab_nonzero :
  forall N u,
    bounded_left_coordinate_family N u ->
    ~ left_cold_slab N u.
Proof.
  intros N u C Hcold.
  assert (HN : (N <= N)%nat) by lia.
  set (x := blcf_coord N u C N HN).
  pose proof (blcf_bounds N u C N HN) as Hbounds.
  pose proof (blcf_hot N u C N HN) as Hhot.
  specialize (Hcold x Hbounds).
  unfold x in Hcold.
  rewrite Hcold in Hhot.
  discriminate.
Qed.

Theorem local_seed_window_realization_left_cold_slab_impossible :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    ~ left_cold_slab N u.
Proof.
  intros N u Hreal.
  apply bounded_left_coordinate_family_implies_left_slab_nonzero.
  exact (local_seed_window_realization_builds_bounded_left_coordinate_family N u Hreal).
Qed.

Record phase2_memory_certificate (N : nat) (u : row) : Type := {
  p2mc_family :
    bounded_left_coordinate_family N u;
  p2mc_nonneutral :
    ~ left_cold_slab N u
}.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Original Sin Theorem                                               *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    A. Start from a bounded realization of the seed window at radius   *)
(*       S (S N).                                                        *)
(*                                                                       *)
(*    B. Use the shell-emission and compactification lemmas to produce   *)
(*       forced left pressure at some bounded levels.                    *)
(*                                                                       *)
(*    C. Package those witnesses as a bounded left-coordinate family.    *)
(*                                                                       *)
(*    D. Deduce that the left slab [-N-3, -3] cannot be identically      *)
(*       cold, and store both facts in phase2_memory_certificate.        *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    forall N u,                                                        *)
(*      local_seed_window_realization (S (S N)) u ->                     *)
(*      phase2_memory_certificate N u                                    *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Every bounded local replay of the seed already carries a finite    *)
(*    left-memory certificate.  The predecessor cannot be semantically   *)
(*    neutral on the left slab: some bounded left coordinate is forced   *)
(*    to remain hot.                                                     *)
(*                                                                       *)
(*************************************************************************)

Theorem original_sin_theorem :
  forall N u,
    local_seed_window_realization (S (S N)) u ->
    phase2_memory_certificate N u.
Proof.
  intros N u Hreal.
  refine
    {| p2mc_family :=
         local_seed_window_realization_builds_bounded_left_coordinate_family N u Hreal;
       p2mc_nonneutral :=
         local_seed_window_realization_left_cold_slab_impossible N u Hreal |}.
Qed.

(*
  Reverse-side finite seeded-prefix layer.

  If a seed reappears after period P, then the shifted canonical trajectory
  starting at time P must match the original seeded prefix for every bounded
  height h.  This packages the intuition "the first five lines repeat"
  without enumerating field values.
*)

Definition seeded_prefix (h : nat) (u : space_time) : Prop :=
  forall t,
    (t <= h)%nat ->
    u t = canonical_row t.

Definition shifted_canonical_trajectory (P : nat) : space_time :=
  fun t => canonical_row (t + P)%nat.

Definition seeded_prefix_repeats_after (h P : nat) : Prop :=
  seeded_prefix h (shifted_canonical_trajectory P).

Lemma seeded_prefix_repeats_after_spec :
  forall h P,
    seeded_prefix_repeats_after h P <->
    forall t,
      (t <= h)%nat ->
      canonical_row (t + P)%nat = canonical_row t.
Proof.
  intros h P.
  unfold seeded_prefix_repeats_after, seeded_prefix, shifted_canonical_trajectory.
  tauto.
Qed.

Lemma seeded_prefix_repeats_after_implies_seed_return :
  forall h P,
    seeded_prefix_repeats_after h P ->
    canonical_row P = seed_row.
Proof.
  intros h P Hrepeat.
  assert (Hzero : (0 <= h)%nat) by lia.
  pose proof (proj1 (seeded_prefix_repeats_after_spec h P) Hrepeat 0%nat Hzero)
    as Hrow.
  rewrite Nat.add_0_l in Hrow.
  rewrite canonical_row_zero in Hrow.
  exact Hrow.
Qed.

Theorem seeded_prefix_repeats_after_positive_period_impossible :
  forall h P,
    (0 < P)%nat ->
    ~ seeded_prefix_repeats_after h P.
Proof.
  intros h [|P] HP Hrepeat.
  - lia.
  - pose proof
      (seeded_prefix_repeats_after_implies_seed_return h (S P) Hrepeat)
      as Hreturn.
    exact (canonical_row_successor_not_seed P Hreturn).
Qed.

(*
  Glitchprojection layer.

  A glitchprojection is a bounded backward cone above the centered seed word.
  Row 0 is the seed row itself.  Each higher row steps to the row below on the
  bounded cone of the appropriate width.  These objects are auxiliary to the
  main Phase 2 endpoint, but they provide the finite reverse-time language used
  to organize compact-trap and hidden-support arguments.
*)

Record glitchprojection (n k : nat) : Type := {
  gp_rows : nat -> row;
  gp_seed_boundary :
    gp_rows 0%nat = seed_row;
  gp_step_legitimacy :
    forall j,
      (j < k)%nat ->
      forall x,
        (Z.abs x <= Z.of_nat (n + k - j))%Z ->
        step (gp_rows (S j)) x = gp_rows j x
}.

Definition glitchprojection_top_row
    {n k : nat} (G : glitchprojection n k) : row :=
  gp_rows n k G k.

Definition glitchprojection_restrict_width
    (m n k : nat)
    (Hmn : (m <= n)%nat)
    (G : glitchprojection n k) : glitchprojection m k.
Proof.
  refine
    {| gp_rows := gp_rows n k G;
       gp_seed_boundary := gp_seed_boundary n k G |}.
  intros j Hj x Hx.
  apply (gp_step_legitimacy n k G j Hj x).
  assert (Hbound_nat : (m + k - j <= n + k - j)%nat) by lia.
  apply Nat2Z.inj_le in Hbound_nat.
  lia.
Defined.

Lemma glitchprojection_restrict_width_top_row :
  forall m n k (Hmn : (m <= n)%nat) (G : glitchprojection n k),
    glitchprojection_top_row (glitchprojection_restrict_width m n k Hmn G) =
    glitchprojection_top_row G.
Proof.
  intros m n k Hmn G.
  reflexivity.
Qed.

(*
  Finite shadow classification for a row relative to the seed outside [-n, n].
*)

Definition extra_left (r : row) (n : nat) : Prop :=
  exists x,
    (x < - Z.of_nat n)%Z /\
    r x <> seed_row x.

Definition extra_right (r : row) (n : nat) : Prop :=
  exists x,
    (Z.of_nat n < x)%Z /\
    r x <> seed_row x.

Inductive profile (r : row) (n : nat) : Prop :=
| profile_equal :
    ~ extra_left r n ->
    ~ extra_right r n ->
    profile r n
| profile_sigma_L :
    extra_left r n ->
    ~ extra_right r n ->
    profile r n
| profile_sigma_R :
    ~ extra_left r n ->
    extra_right r n ->
    profile r n
| profile_pi :
    extra_left r n ->
    extra_right r n ->
    profile r n.

Lemma profile_classification :
  forall r n,
    profile r n.
Proof.
  intros r n.
  destruct (classic (extra_left r n)) as [Hleft | Hnleft];
  destruct (classic (extra_right r n)) as [Hright | Hnright].
  - exact (profile_pi r n Hleft Hright).
  - exact (profile_sigma_L r n Hleft Hnright).
  - exact (profile_sigma_R r n Hnleft Hright).
  - exact (profile_equal r n Hnleft Hnright).
Qed.

Lemma extra_left_monotone :
  forall r n m,
    (m <= n)%nat ->
    extra_left r n ->
    extra_left r m.
Proof.
  intros r n m Hmn [x [Hx Hneq]].
  exists x.
  split.
  - lia.
  - exact Hneq.
Qed.

Lemma extra_right_monotone :
  forall r n m,
    (m <= n)%nat ->
    extra_right r n ->
    extra_right r m.
Proof.
  intros r n m Hmn [x [Hx Hneq]].
  exists x.
  split.
  - lia.
  - exact Hneq.
Qed.

Definition glitchprojection_extra_left
    {n k : nat} (G : glitchprojection n k) : Prop :=
  extra_left (glitchprojection_top_row G) n.

Definition glitchprojection_extra_right
    {n k : nat} (G : glitchprojection n k) : Prop :=
  extra_right (glitchprojection_top_row G) n.

Definition glitchprojection_bilateral
    {n k : nat} (G : glitchprojection n k) : Prop :=
  glitchprojection_extra_left G /\ glitchprojection_extra_right G.

Definition glitchprojection_profile
    {n k : nat} (G : glitchprojection n k) : Prop :=
  profile (glitchprojection_top_row G) n.

Lemma glitchprojection_profile_classification :
  forall n k (G : glitchprojection n k),
    glitchprojection_profile G.
Proof.
  intros n k G.
  unfold glitchprojection_profile.
  apply profile_classification.
Qed.

Lemma glitchprojection_restrict_preserves_extra_left :
  forall m n k (Hmn : (m <= n)%nat) (G : glitchprojection n k),
    glitchprojection_extra_left G ->
    glitchprojection_extra_left (glitchprojection_restrict_width m n k Hmn G).
Proof.
  intros m n k Hmn G Hleft.
  unfold glitchprojection_extra_left in *.
  rewrite glitchprojection_restrict_width_top_row.
  now apply (extra_left_monotone (glitchprojection_top_row G) n m Hmn).
Qed.

Lemma glitchprojection_restrict_preserves_extra_right :
  forall m n k (Hmn : (m <= n)%nat) (G : glitchprojection n k),
    glitchprojection_extra_right G ->
    glitchprojection_extra_right (glitchprojection_restrict_width m n k Hmn G).
Proof.
  intros m n k Hmn G Hright.
  unfold glitchprojection_extra_right in *.
  rewrite glitchprojection_restrict_width_top_row.
  now apply (extra_right_monotone (glitchprojection_top_row G) n m Hmn).
Qed.

Lemma glitchprojection_opposite_sides_force_bilateral_on_smaller_width :
  forall m n k (Hmn : (m <= n)%nat) (G : glitchprojection n k),
    glitchprojection_extra_left G ->
    glitchprojection_extra_right
      (glitchprojection_restrict_width m n k Hmn G) ->
    glitchprojection_bilateral
      (glitchprojection_restrict_width m n k Hmn G).
Proof.
  intros m n k Hmn G Hleft Hright.
  split.
  - apply glitchprojection_restrict_preserves_extra_left; assumption.
  - exact Hright.
Qed.

(*
  A bounded replay fragment fixes one alleged period and a finite time horizon.
  Only the centered observables are constrained here; the future refinement is
  expected to replace this with a genuinely finite cone object.
*)

Record bounded_periodic_replay_fragment (n P H : nat) : Type := {
  bprf_period_pos : (0 < P)%nat;
  bprf_space_time : space_time;
  bprf_matches_seeded_window :
    forall t,
      (t <= H)%nat ->
      replay_window bprf_space_time n t = center_window n t;
  bprf_periodic_on_horizon :
    forall t,
      (t + P <= H)%nat ->
      replay_window bprf_space_time n (t + P)%nat =
      replay_window bprf_space_time n t
}.

(*
  A seed-forcing glitch is the local interface responsible for creating a seed
  event.  The exact finite pattern is intentionally left abstract here; R05 is
  only the naming layer for the later Rocq realization.
*)

Definition seed_forcing_glitch
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) : glitch_site -> Prop :=
  fun g =>
    seed_creation_triplet
      (bprf_space_time n P H F (gs_time g))
      (gs_center g).

Definition compact_center_trap_on_fragment
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) (g : glitch_site) : Prop :=
  compact_fall_trap
    (bprf_space_time n P H F (gs_time g))
    (gs_center g).

(*
  Hidden support is the many-to-one escape hatch: extra predecessor material
  outside the compact center trap.  It becomes causally relevant as soon as it
  lies inside the backward light cone of one replay cycle.
*)

Definition hidden_support_at (r : row) (c x : Z) : Prop :=
  x <> (c - 1)%Z /\
  x <> c /\
  x <> (c + 1)%Z /\
  r x = true.

Definition hidden_support_on_fragment
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) (g : glitch_site) (x : Z) : Prop :=
  hidden_support_at
    (bprf_space_time n P H F (gs_time g))
    (gs_center g)
    x.

Definition causally_relevant_hidden_support
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) (g : glitch_site) (x : Z) : Prop :=
  hidden_support_on_fragment n P H F g x /\
  (Z.abs (x - gs_center g) <= Z.of_nat P)%Z.

Definition relevant_hidden_support_distance
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) (g : glitch_site) (d : nat) : Prop :=
  exists x,
    causally_relevant_hidden_support n P H F g x /\
    Z.to_nat (Z.abs (x - gs_center g)) = d.

Definition minimal_relevant_hidden_support_distance
    (n P H : nat) (F : bounded_periodic_replay_fragment n P H) (g : glitch_site) (d : nat) : Prop :=
  relevant_hidden_support_distance n P H F g d /\
  forall d',
    relevant_hidden_support_distance n P H F g d' ->
    (d <= d')%nat.

Lemma causally_relevant_hidden_support_has_distance :
  forall n P H (F : bounded_periodic_replay_fragment n P H) g x,
    causally_relevant_hidden_support n P H F g x ->
    exists d,
      relevant_hidden_support_distance n P H F g d.
Proof.
  intros n P H F g x Hrelevant.
  exists (Z.to_nat (Z.abs (x - gs_center g))).
  exists x.
  split.
  - exact Hrelevant.
  - reflexivity.
Qed.

Lemma relevant_hidden_support_distance_has_minimal :
  forall n P H (F : bounded_periodic_replay_fragment n P H) g d,
    relevant_hidden_support_distance n P H F g d ->
    exists d',
      minimal_relevant_hidden_support_distance n P H F g d'.
Proof.
  intros n P H F g d Hd.
  revert d Hd.
  apply (well_founded_induction
    lt_wf
    (fun m =>
      relevant_hidden_support_distance n P H F g m ->
      exists d',
        minimal_relevant_hidden_support_distance n P H F g d')).
  intros m IH Hm.
  destruct (classic
    (exists d',
      relevant_hidden_support_distance n P H F g d' /\
      (d' < m)%nat)) as [Hsmaller | Hminimal].
  - destruct Hsmaller as [d' [Hd' Hd'lt]].
    exact (IH d' Hd'lt Hd').
  - exists m.
    split.
    + exact Hm.
    + intros d' Hd'.
      destruct (le_lt_dec m d') as [Hle | Hlt].
      * exact Hle.
      * exfalso.
        apply Hminimal.
        exists d'.
        split.
        -- exact Hd'.
        -- exact Hlt.
Qed.

Lemma causally_relevant_hidden_support_has_minimal_distance :
  forall n P H (F : bounded_periodic_replay_fragment n P H) g x,
    causally_relevant_hidden_support n P H F g x ->
    exists d,
      minimal_relevant_hidden_support_distance n P H F g d.
Proof.
  intros n P H F g x Hrelevant.
  destruct (causally_relevant_hidden_support_has_distance n P H F g x Hrelevant)
    as [d Hd].
  now apply (relevant_hidden_support_distance_has_minimal n P H F g d Hd).
Qed.

Lemma hidden_support_is_outside_compact_trap :
  forall r c x,
    hidden_support_at r c x ->
    (2 <= Z.to_nat (Z.abs (x - c)))%nat.
Proof.
  intros r c x [Hneq_left [Hneq_mid [Hneq_right _]]].
  apply Nat2Z.inj_le.
  rewrite Z2Nat.id by apply Z.abs_nonneg.
  destruct (Zabs_spec (x - c)) as [[Hnonneg Habs] | [Hneg Habs]];
  rewrite Habs;
  assert (x <> c - 1)%Z by exact Hneq_left;
  assert (x <> c)%Z by exact Hneq_mid;
  assert (x <> c + 1)%Z by exact Hneq_right;
  lia.
Qed.

Lemma minimal_relevant_hidden_support_distance_ge_2 :
  forall n P H (F : bounded_periodic_replay_fragment n P H) g d,
    minimal_relevant_hidden_support_distance n P H F g d ->
    (2 <= d)%nat.
Proof.
  intros n P H F g d [[x [[Hhidden _] Hdist]] _].
  rewrite <- Hdist.
  unfold causally_relevant_hidden_support, hidden_support_on_fragment in Hhidden.
  exact (hidden_support_is_outside_compact_trap
    (bprf_space_time n P H F (gs_time g))
    (gs_center g)
    x
    Hhidden).
Qed.

Lemma compact_center_trap_on_fragment_impossible :
  forall n P H (F : bounded_periodic_replay_fragment n P H) g,
    compact_center_trap_on_fragment n P H F g ->
    False.
Proof.
  intros n P H F g.
  apply compact_fall_trap_impossible.
Qed.

End Glitch_Compactness.
