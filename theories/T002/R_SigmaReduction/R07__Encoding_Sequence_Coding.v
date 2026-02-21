(* R07__Sequence_Coding.v *)

From Coq Require Import Arith List.
Import ListNotations.

From T002 Require Import
  R03__Encoding_Beta
  R06__Encoding_Formula_Coding
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker.

Definition f_i (c d i : nat) : nat := beta c d i.

Lemma beta_trace_exists_for_form_codes :
  forall (pf : Proof),
    exists c,
      forall i,
        i < length pf ->
        f_i c (beta_d (map enc_form pf)) i = enc_form (nth i pf Bot).
Proof.
  intro pf.
  set (codes := map enc_form pf).
  destruct (beta_exists codes) as [c Hc].
  exists c.
  intros i Hi.
  unfold f_i.
  assert (Hilen : i < length codes).
  { unfold codes. rewrite length_map. exact Hi. }
  specialize (Hc i Hilen).
  rewrite Hc.
  unfold codes.
  rewrite (nth_indep (n := i) (map enc_form pf) 0 (enc_form Bot)).
  2:{ rewrite length_map. exact Hi. }
  rewrite map_nth.
  reflexivity.
Qed.