(* R06__3rd_Corollary.v *)

From Coq Require Import Arith Bool List.
Import ListNotations.

From T004 Require Import
  R01__Phase_One
  R02__Phase_Two
  R03__Phase_Three.

(*************************************************************************)
(*                                                                       *)
(*  Proofcase / Rule 30 3rd Corollary                                    *)
(*                                                                       *)
(*  Finite provenance / observation-only corollary layer.                *)
(*                                                                       *)
(*  The file has two strands.                                            *)
(*                                                                       *)
(*     (a) Center-strip-free shell proxy.                                *)
(*                                                                       *)
(*         The visible four-bit outer shell around the hidden center     *)
(*         triplet already decides a coarse syntactic question           *)
(*         "was this manipulated?", and Phase 2 proves every bounded     *)
(*         local seed-window realization answers that question           *)
(*         positively.                                                   *)
(*                                                                       *)
(*     (b) Observation-only reverse provenance ambiguity.                *)
(*                                                                       *)
(*         A visible canonical observation does not determine a unique   *)
(*         reverse predecessor carrier.  Instead it supports an exact    *)
(*         four-point family indexed by right-boundary bits, containing  *)
(*         the canonical reverse predecessor and distinct tampered       *)
(*         alternatives.  This is the structural reason                  *)
(*         observation-only tamper checking fails.                       *)
(*                                                                       *)
(*************************************************************************)

Section Third_Corollary.

Definition shell_signature_unmanipulated : list bit :=
  [false; false; false; false].

Definition syntactically_manipulated_signature (sig : list bit) : Prop :=
  sig <> shell_signature_unmanipulated.

Definition syntactically_manipulated_signatureb (sig : list bit) : bool :=
  match sig with
  | [a; b; c; d] => a || b || c || d
  | _ => false
  end.

Lemma syntactically_manipulated_signatureb_spec :
  forall sig,
    length sig = 4%nat ->
    syntactically_manipulated_signatureb sig = true <->
    syntactically_manipulated_signature sig.
Proof.
  intros sig Hlen.
  destruct sig as [|a [|b [|c [|d [|e sig']]]]]; simpl in Hlen; try discriminate.
  split; intro H.
  - unfold syntactically_manipulated_signature, shell_signature_unmanipulated.
    destruct a, b, c, d; simpl in H; try discriminate; intro Heq; inversion Heq.
  - unfold syntactically_manipulated_signature, shell_signature_unmanipulated in H.
    destruct a, b, c, d; simpl; try reflexivity.
    exfalso.
    apply H.
    reflexivity.
Qed.

Definition center_strip_free_signature (N : nat) (u : row) : list bit :=
  outer_shell_signature N u.

Definition center_strip_free_manipulated (N : nat) (u : row) : Prop :=
  syntactically_manipulated_signature (center_strip_free_signature N u).

Definition center_strip_free_manipulatedb (N : nat) (u : row) : bool :=
  syntactically_manipulated_signatureb (center_strip_free_signature N u).

Lemma center_strip_free_signature_length :
  forall N u,
    length (center_strip_free_signature N u) = 4%nat.
Proof.
  intros N u.
  reflexivity.
Qed.

Theorem center_strip_free_manipulatedb_spec :
  forall N u,
    center_strip_free_manipulatedb N u = true <->
    center_strip_free_manipulated N u.
Proof.
  intros N u.
  unfold center_strip_free_manipulatedb,
    center_strip_free_manipulated,
    center_strip_free_signature.
  apply syntactically_manipulated_signatureb_spec.
  reflexivity.
Qed.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Center-Strip-Free Manipulation Question Is Decidable               *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    (a) Reduce the visible shell question to the Boolean test          *)
(*         `center_strip_free_manipulatedb`.                             *)
(*                                                                       *)
(*    (b) Use the four-bit specification lemma to identify that          *)
(*        boolean with nontriviality of the outer shell signature.       *)
(*                                                                       *)
(*    (c) Case-split on the Boolean output.                              *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    forall N u,                                                        *)
(*      { center_strip_free_manipulated N u } +                          *)
(*      { ~ center_strip_free_manipulated N u }                          *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    Once the center triplet is hidden, the residual visible shell      *)
(*    still supports a finite yes/no syntactic manipulation query.       *)
(*                                                                       *)
(*************************************************************************)

Theorem manipulation_question_decidable_without_center_strip :
  forall N u,
    { center_strip_free_manipulated N u } +
    { ~ center_strip_free_manipulated N u }.
Proof.
  intros N u.
  destruct (center_strip_free_manipulatedb N u) eqn:Hb.
  - left.
    apply (proj1 (center_strip_free_manipulatedb_spec N u)).
    exact Hb.
  - right.
    intro Hmanipulated.
    apply (proj2 (center_strip_free_manipulatedb_spec N u)) in Hmanipulated.
    rewrite Hb in Hmanipulated.
    discriminate.
Qed.

Theorem local_seed_window_realization_forces_center_strip_free_manipulation :
  forall N u,
    local_seed_window_realization (S N) u ->
    center_strip_free_manipulated N u.
Proof.
  intros N u Hreal.
  unfold center_strip_free_manipulated,
    syntactically_manipulated_signature,
    center_strip_free_signature,
    shell_signature_unmanipulated.
  exact (local_seed_window_realization_requires_nonzero_shell_signature N u Hreal).
Qed.

Theorem local_seed_window_realization_forces_center_strip_free_manipulationb :
  forall N u,
    local_seed_window_realization (S N) u ->
    center_strip_free_manipulatedb N u = true.
Proof.
  intros N u Hreal.
  apply (proj2 (center_strip_free_manipulatedb_spec N u)).
  exact
    (local_seed_window_realization_forces_center_strip_free_manipulation
      N u Hreal).
Qed.

End Third_Corollary.

Section Observation_Only_Impossibility.

Definition canonical_observation (R T : nat) : list bit :=
  center_window R (S T).

Definition canonical_reverse_predecessor (R T : nat) : list bit :=
  rev (predecessor_carrier_window R (canonical_row T)).

Definition canonical_reverse_predecessor_from_boundary
    (R T : nat) (b c : bit) : list bit :=
  reconstruct_carrier_rev_from (rev (canonical_observation R T)) b c.

Definition reverse_predecessor_realizes_canonical_observation
    (R T : nat) (carrier_rev : list bit) : Prop :=
  rule30_window_rev carrier_rev = rev (canonical_observation R T).

Definition reverse_tampered_against_canonical
    (R T : nat) (carrier_rev : list bit) : Prop :=
  reverse_predecessor_realizes_canonical_observation R T carrier_rev /\
  carrier_rev <> canonical_reverse_predecessor R T.

Definition observation_only_tamper_checker
    (R T : nat) (checker : list bit -> bool) : Prop :=
  forall carrier_rev,
    reverse_predecessor_realizes_canonical_observation R T carrier_rev ->
    (checker (canonical_observation R T) = true <->
     carrier_rev <> canonical_reverse_predecessor R T).

Definition canonical_reverse_predecessor_family
    (R T : nat) : list (list bit) :=
  map
    (fun bc =>
       canonical_reverse_predecessor_from_boundary R T (fst bc) (snd bc))
    boundary_signature_pool.

Lemma canonical_observation_length :
  forall R T,
    length (canonical_observation R T) = S (2 * R).
Proof.
  intros R T.
  unfold canonical_observation, center_window, centered_coords.
  rewrite length_map.
  rewrite z_segment_length.
  reflexivity.
Qed.

Lemma canonical_reverse_predecessor_from_boundary_injective :
  forall R T b1 c1 b2 c2,
    canonical_reverse_predecessor_from_boundary R T b1 c1 =
    canonical_reverse_predecessor_from_boundary R T b2 c2 ->
    b1 = b2 /\ c1 = c2.
Proof.
  intros R T b1 c1 b2 c2 Heq.
  unfold canonical_reverse_predecessor_from_boundary in Heq.
  destruct
    (reconstruct_carrier_rev_from_starts_with_boundary
      (rev (canonical_observation R T)) b1 c1)
    as [rest1 Hstart1].
  destruct
    (reconstruct_carrier_rev_from_starts_with_boundary
      (rev (canonical_observation R T)) b2 c2)
    as [rest2 Hstart2].
  rewrite Hstart1 in Heq.
  rewrite Hstart2 in Heq.
  inversion Heq; subst.
  split; reflexivity.
Qed.

Lemma canonical_reverse_predecessor_family_length :
  forall R T,
    length (canonical_reverse_predecessor_family R T) = 4%nat.
Proof.
  intros R T.
  unfold canonical_reverse_predecessor_family.
  rewrite length_map.
  exact boundary_signature_pool_length.
Qed.

Lemma canonical_reverse_predecessor_family_NoDup :
  forall R T,
    NoDup (canonical_reverse_predecessor_family R T).
Proof.
  intros R T.
  unfold canonical_reverse_predecessor_family.
  apply (NoDup_map_injective
    (bit * bit)
    (list bit)
    (fun bc =>
       canonical_reverse_predecessor_from_boundary R T (fst bc) (snd bc))
    boundary_signature_pool).
  - exact boundary_signature_pool_NoDup.
  - intros [b1 c1] [b2 c2] Heq.
    simpl in Heq.
    destruct
      (canonical_reverse_predecessor_from_boundary_injective
        R T b1 c1 b2 c2 Heq)
      as [Hb Hc].
    subst b2 c2.
    reflexivity.
Qed.

Theorem canonical_reverse_predecessor_realizes_canonical_observation :
  forall R T,
    reverse_predecessor_realizes_canonical_observation
      R T (canonical_reverse_predecessor R T).
Proof.
  intros R T.
  unfold reverse_predecessor_realizes_canonical_observation,
    canonical_reverse_predecessor,
    canonical_observation.
  rewrite rule30_window_rev_on_centered_carrier.
  rewrite row_window_step_canonical_row.
  reflexivity.
Qed.

Theorem boundary_parametrized_reverse_predecessor_realizes_canonical_observation :
  forall R T b c,
    reverse_predecessor_realizes_canonical_observation
      R T (canonical_reverse_predecessor_from_boundary R T b c).
Proof.
  intros R T b c.
  unfold reverse_predecessor_realizes_canonical_observation,
    canonical_reverse_predecessor_from_boundary.
  apply rule30_window_rev_reconstructs_outputs.
Qed.

Theorem reverse_predecessor_realizing_canonical_observation_has_boundary_parameters :
  forall R T carrier_rev,
    reverse_predecessor_realizes_canonical_observation R T carrier_rev ->
    exists b c,
      carrier_rev = canonical_reverse_predecessor_from_boundary R T b c.
Proof.
  intros R T carrier_rev Hreal.
  assert (Hlen_obs : length (rev (canonical_observation R T)) <> 0%nat).
  {
    rewrite length_rev.
    rewrite canonical_observation_length.
    discriminate.
  }
  destruct carrier_rev as [|c carrier_rev].
  - simpl in Hreal.
    exfalso.
    apply Hlen_obs.
    rewrite <- Hreal.
    reflexivity.
  - destruct carrier_rev as [|b carrier_rev].
    + simpl in Hreal.
      exfalso.
      apply Hlen_obs.
      rewrite <- Hreal.
      reflexivity.
    + destruct carrier_rev as [|a rest].
      * simpl in Hreal.
        exfalso.
        apply Hlen_obs.
        rewrite <- Hreal.
        reflexivity.
      * exists b, c.
        unfold canonical_reverse_predecessor_from_boundary.
        exact
          (rule30_window_rev_determined_by_boundary
            (rev (canonical_observation R T)) b c (a :: rest) Hreal).
Qed.

Theorem reverse_predecessor_realizing_canonical_observation_in_four_candidate_family :
  forall R T carrier_rev,
    reverse_predecessor_realizes_canonical_observation R T carrier_rev ->
    In carrier_rev (canonical_reverse_predecessor_family R T).
Proof.
  intros R T carrier_rev Hreal.
  unfold canonical_reverse_predecessor_family.
  destruct
    (reverse_predecessor_realizing_canonical_observation_has_boundary_parameters
      R T carrier_rev Hreal)
    as [b [c Hcarrier]].
  subst carrier_rev.
  destruct b, c; simpl; auto.
Qed.

Theorem reverse_predecessor_realizes_canonical_observation_iff_in_family :
  forall R T carrier_rev,
    reverse_predecessor_realizes_canonical_observation R T carrier_rev <->
    In carrier_rev (canonical_reverse_predecessor_family R T).
Proof.
  intros R T carrier_rev.
  split.
  - apply reverse_predecessor_realizing_canonical_observation_in_four_candidate_family.
  - intro Hin.
    unfold canonical_reverse_predecessor_family, boundary_signature_pool in Hin.
    simpl in Hin.
    destruct Hin as [Hff | [Hft | [Htf | [Htt | []]]]];
      subst carrier_rev;
      apply boundary_parametrized_reverse_predecessor_realizes_canonical_observation.
Qed.

Theorem canonical_reverse_predecessor_in_family :
  forall R T,
    In (canonical_reverse_predecessor R T)
       (canonical_reverse_predecessor_family R T).
Proof.
  intros R T.
  apply (proj1
    (reverse_predecessor_realizes_canonical_observation_iff_in_family
      R T (canonical_reverse_predecessor R T))).
  apply canonical_reverse_predecessor_realizes_canonical_observation.
Qed.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    Canonical Observation Has Exactly Four Reverse Predecessors        *)
(*                                                                       *)
(*                              PROOF ROUTE                              *)
(*                                                                       *)
(*    (a) Parameterize every reverse predecessor realizing the visible   *)
(*        canonical observation by its two right-boundary bits.          *)
(*                                                                       *)
(*    (b) Reconstruct a realizing reverse carrier from each of the       *)
(*        four possible boundary signatures.                             *)
(*                                                                       *)
(*    (c) Use boundary injectivity to show these four realizers are      *)
(*        distinct.                                                      *)
(*                                                                       *)
(*    (d) Conclude that realization is equivalent to membership in a     *)
(*        four-point NoDup family.                                       *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    forall R T,                                                        *)
(*      length (canonical_reverse_predecessor_family R T) = 4 /\         *)
(*      NoDup (canonical_reverse_predecessor_family R T) /\              *)
(*      forall carrier_rev,                                              *)
(*        reverse_predecessor_realizes_canonical_observation             *)
(*          R T carrier_rev <->                                          *)
(*        In carrier_rev (canonical_reverse_predecessor_family R T)      *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    The visible canonical window does not hide one unknown reverse     *)
(*    predecessor carrier but an exact four-way boundary-indexed         *)
(*    ambiguity class.                                                   *)
(*                                                                       *)
(*************************************************************************)

Theorem canonical_observation_has_exactly_four_reverse_predecessor_carriers :
  forall R T,
    length (canonical_reverse_predecessor_family R T) = 4%nat /\
    NoDup (canonical_reverse_predecessor_family R T) /\
    forall carrier_rev,
      reverse_predecessor_realizes_canonical_observation R T carrier_rev <->
      In carrier_rev (canonical_reverse_predecessor_family R T).
Proof.
  intros R T.
  split.
  - apply canonical_reverse_predecessor_family_length.
  - split.
    + apply canonical_reverse_predecessor_family_NoDup.
    + intro carrier_rev.
      apply reverse_predecessor_realizes_canonical_observation_iff_in_family.
Qed.

Theorem canonical_observation_has_tampered_reverse_predecessor :
  forall R T,
    exists carrier_rev,
      reverse_tampered_against_canonical R T carrier_rev.
Proof.
  intros R T.
  destruct
    (predecessor_carrier_window_has_right_boundary_signature
      R (canonical_row T))
    as [b [c [rest [Hsig Hrev]]]].
  exists (canonical_reverse_predecessor_from_boundary R T b (negb c)).
  split.
  - apply boundary_parametrized_reverse_predecessor_realizes_canonical_observation.
  - unfold canonical_reverse_predecessor,
      canonical_reverse_predecessor_from_boundary.
    intro Heq.
    destruct
      (reconstruct_carrier_rev_from_starts_with_boundary
        (rev (canonical_observation R T)) b (negb c))
      as [rest' Hstart].
    rewrite Hrev in Heq.
    rewrite Hstart in Heq.
    inversion Heq.
    destruct c; discriminate.
Qed.

(*************************************************************************)
(*                                                                       *)
(*                                THEOREM                                *)
(*                                                                       *)
(*    No Observation-Only Tamper Checker                                 *)
(*                                                                       *)
(*                                 PROOF                                 *)
(*                                                                       *)
(*    (a) Evaluate the hypothetical checker on the canonical reverse     *)
(*        predecessor, which forces the answer false.                    *)
(*                                                                       *)
(*    (b) Use the reverse ambiguity layer to obtain a distinct           *)
(*        tampered reverse predecessor realizing the same visible        *)
(*        observation.                                                   *)
(*                                                                       *)
(*    (c) Evaluate the checker on that tampered carrier, which forces    *)
(*        the same observation to be answered true.                      *)
(*                                                                       *)
(*    (d) Contradict single-valuedness of the observation-checker.       *)
(*                                                                       *)
(*                              REALIZATION                              *)
(*                                                                       *)
(*    forall R T checker,                                                *)
(*      ~ observation_only_tamper_checker R T checker                    *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    No decision procedure that sees only the visible canonical window  *)
(*    can distinguish canonical hidden predecessor carriers from         *)
(*    tampered hidden predecessor carriers.                              *)
(*                                                                       *)
(*************************************************************************)

Theorem no_observation_only_tamper_checker :
  forall R T checker,
    ~ observation_only_tamper_checker R T checker.
Proof.
  intros R T checker Hchecker.
  pose proof
    (canonical_reverse_predecessor_realizes_canonical_observation R T)
    as Hcanonical.
  specialize (Hchecker (canonical_reverse_predecessor R T) Hcanonical)
    as Hcanonical_spec.
  assert (Hnot_true : checker (canonical_observation R T) <> true).
  {
    intro Hvalue.
    apply (proj1 Hcanonical_spec Hvalue).
    reflexivity.
  }
  destruct
    (canonical_observation_has_tampered_reverse_predecessor R T)
    as [carrier_rev [Htampered_realizes Htampered_neq]].
  specialize (Hchecker carrier_rev Htampered_realizes) as Htampered_spec.
  apply Hnot_true.
  apply (proj2 Htampered_spec).
  exact Htampered_neq.
Qed.

End Observation_Only_Impossibility.
