(* R05__Hilbert_Checker.v *)

From Coq Require Import Init.Logic Arith List Bool.
Import ListNotations.

From T002 Require Import R04__Verification_Hilbert_Syntax.

Definition Proof : Type := list Form.

Fixpoint existsb_local {A : Type} (p : A -> bool) (xs : list A) : bool :=
  match xs with
  | [] => false
  | x :: xs' => orb (p x) (existsb_local p xs')
  end.

Lemma existsb_local_sound :
  forall (A : Type) (p : A -> bool) (xs : list A),
    existsb_local p xs = true ->
    exists x : A, In x xs /\ p x = true.
Proof.
  intros A p xs H.
  induction xs as [|x xs IH].
  - discriminate.
  - simpl in H.
    unfold orb in H.
    destruct (p x) eqn:Px.
    + exists x. split; [left; reflexivity|exact Px].
    + specialize (IH H).
      destruct IH as [y [Hyin Hyp]].
      exists y. split; [right; exact Hyin|exact Hyp].
Qed.

Definition mp_witness (ctx : list Form) (phi : Form) : bool :=
  existsb_local
    (fun psi =>
       existsb_local
         (fun chi =>
            match chi with
            | F_Imp X Y =>
                andb (form_eqb X psi) (form_eqb Y phi)
            | _ => false
            end)
         ctx)
    ctx.

Fixpoint check_lines (ctx : list Form) (pf : Proof) : bool :=
  match pf with
  | [] => true
  | line :: rest =>
      let ok_line := orb (is_axiom line) (mp_witness ctx line) in
      andb ok_line (check_lines (line :: ctx) rest)
  end.

Fixpoint last_opt (pf : Proof) : option Form :=
  match pf with
  | [] => None
  | [x] => Some x
  | _ :: xs => last_opt xs
  end.

Definition check (pf : Proof) (goal : Form) : bool :=
  match last_opt pf with
  | None => false
  | Some last => andb (check_lines [] pf) (form_eqb last goal)
  end.

Module Tests.

  Definition lnil : Proof := [].
  Definition lcons (x : Form) (xs : Proof) : Proof := x :: xs.
  Definition l1 (x : Form) : Proof := lcons x lnil.
  Definition l3 (a b c : Form) : Proof := lcons a (lcons b (lcons c lnil)).

  Definition A0 : Form := Imp Bot Bot.
  Definition B0 : Form := Imp Bot (Imp Bot Bot).

  Example test_check_empty_rejects :
    check lnil A0 = false.
  Proof. vm_compute. reflexivity. Qed.

  Example test_is_axiom_efq :
    is_axiom (Imp Bot Bot) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example test_check_single_axiom :
    check (l1 A0) A0 = true.
  Proof. vm_compute. reflexivity. Qed.

  Definition line1 : Form := A0.
  Definition line2 : Form := Imp A0 (Imp B0 A0).
  Definition line3 : Form := Imp B0 A0.

  Example test_check_mp_script :
    check (l3 line1 line2 line3) line3 = true.
  Proof. vm_compute. reflexivity. Qed.

End Tests.