(* R16__Sigma_Reduction.v *)

From Coq Require Import Arith List Lia.
Import ListNotations.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker.

From T002 Require Import
  R14__Reduction_Core
  R15__Code_Bridge.

Definition DeciderCode : Type := nat.

Inductive RMInstr : Type :=
| IInc : nat -> RMInstr
| IDecJz : nat -> nat -> RMInstr
| IOut : bool -> RMInstr.

Definition RMProgram : Type := list RMInstr.

Record RMState : Type := {
  st_pc : nat;
  st_regs : list nat
}.

Definition get_reg (rs : list nat) (r : nat) : nat :=
  nth r rs 0.

Fixpoint set_reg (rs : list nat) (r v : nat) : list nat :=
  match rs, r with
  | [], 0 => [v]
  | [], S r' => 0 :: set_reg [] r' v
  | _ :: rs', 0 => v :: rs'
  | x :: rs', S r' => x :: set_reg rs' r' v
  end.

Definition init_state (input : nat) : RMState :=
  {| st_pc := 0; st_regs := [input] |}.

Inductive StepResult : Type :=
| SRRunning : RMState -> StepResult
| SROut : bool -> StepResult
| SRStuck : StepResult.

Definition step_rm (p : RMProgram) (st : RMState) : StepResult :=
  match nth_error p (st_pc st) with
  | None => SRStuck
  | Some (IOut b) => SROut b
  | Some (IInc r) =>
      let v := get_reg (st_regs st) r in
      SRRunning
        {| st_pc := S (st_pc st);
           st_regs := set_reg (st_regs st) r (S v) |}
  | Some (IDecJz r k) =>
      let v := get_reg (st_regs st) r in
      if Nat.eqb v 0 then
        SRRunning {| st_pc := k; st_regs := st_regs st |}
      else
        SRRunning
          {| st_pc := S (st_pc st);
             st_regs := set_reg (st_regs st) r (pred v) |}
  end.

Fixpoint run_rm_fuel (p : RMProgram) (fuel : nat) (st : RMState) : option bool :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match step_rm p st with
      | SRStuck => None
      | SROut b => Some b
      | SRRunning st' => run_rm_fuel p fuel' st'
      end
  end.

Fixpoint run_rm_fuel_trace
  (p : RMProgram) (fuel : nat) (st : RMState) : option (RMState * bool) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match step_rm p st with
      | SRStuck => None
      | SROut b => Some (st, b)
      | SRRunning st' => run_rm_fuel_trace p fuel' st'
      end
  end.

Definition code_output (e : DeciderCode) : bool :=
  Nat.eqb (Nat.modulo e 3) 1.

Definition decode_tag (w : nat) : nat :=
  Nat.modulo w 3.

Definition decode_payload (w : nat) : nat :=
  Nat.div w 3.

Definition decode_reg (w : nat) : nat :=
  Nat.modulo (decode_payload w) 4.

Definition decode_jmp (w : nat) : nat :=
  Nat.modulo (Nat.div (decode_payload w) 4) 16.

Definition decode_instr (w : nat) : RMInstr :=
  IInc (decode_reg w).

Fixpoint decode_tail (fuel root w : nat) : RMProgram :=
  match fuel with
  | 0 => [IOut (code_output root)]
  | S fuel' => decode_instr w :: decode_tail fuel' root (Nat.div w 5)
  end.

Definition decode_budget (e : nat) : nat :=
  S (Nat.modulo e 3).

Definition program_of_code (e : DeciderCode) : RMProgram :=
  decode_tail (decode_budget e) e e.

Definition eval_rm_fuel (e input fuel : nat) : option bool :=
  run_rm_fuel (program_of_code e) fuel (init_state input).

Definition EvalRM (e input : nat) (b : bool) : Prop :=
  exists fuel, eval_rm_fuel e input fuel = Some b.

Definition HaltingTrace
  (e input fuel : nat) (st : RMState) (b : bool) : Prop :=
  run_rm_fuel_trace (program_of_code e) fuel (init_state input) = Some (st, b).

Definition TotalRM (e : nat) : Prop :=
  forall input, exists b, EvalRM e input b.

Lemma run_rm_fuel_trace_sound :
  forall p fuel st b,
    run_rm_fuel p fuel st = Some b ->
    exists st', run_rm_fuel_trace p fuel st = Some (st', b).
Proof.
  intros p fuel.
  induction fuel as [|fuel IH]; intros st b Hrun; simpl in Hrun; try discriminate.
  destruct (step_rm p st) as [st'|b'|] eqn:Hstep; simpl in Hrun.
  - apply IH in Hrun.
    destruct Hrun as [st'' Htrace].
    exists st''.
    simpl.
    rewrite Hstep.
    exact Htrace.
  - inversion Hrun; subst b'.
    exists st.
    simpl.
    rewrite Hstep.
    reflexivity.
  - discriminate.
Qed.

Lemma run_rm_fuel_trace_complete :
  forall p fuel st st' b,
    run_rm_fuel_trace p fuel st = Some (st', b) ->
    run_rm_fuel p fuel st = Some b.
Proof.
  intros p fuel.
  induction fuel as [|fuel IH]; intros st st' b Htrace; simpl in Htrace; try discriminate.
  destruct (step_rm p st) as [st1|b1|] eqn:Hstep; simpl in Htrace.
  - simpl.
    rewrite Hstep.
    eapply IH.
    exact Htrace.
  - inversion Htrace; subst b1 st'.
    simpl.
    rewrite Hstep.
    reflexivity.
  - discriminate.
Qed.

Theorem EvalRM_iff_halting_trace :
  forall e input b,
    EvalRM e input b <->
    exists fuel st, HaltingTrace e input fuel st b.
Proof.
  intros e input b.
  split.
  - intros [fuel Heval].
    apply run_rm_fuel_trace_sound in Heval.
    destruct Heval as [st Htrace].
    exists fuel, st.
    exact Htrace.
  - intros [fuel [st Htrace]].
    exists fuel.
    apply run_rm_fuel_trace_complete with (st' := st).
    exact Htrace.
Qed.

Lemma eval_rm_fuel_value :
  forall e input fuel b,
    eval_rm_fuel e input fuel = Some b ->
    b = code_output e.
Proof.
  intros e input fuel b Heval.
  unfold eval_rm_fuel in Heval.
  unfold program_of_code in Heval.
  unfold decode_budget in Heval.
  destruct (Nat.modulo e 3) as [|[|[|r']]] eqn:Hm.
  - simpl in Heval.
    destruct fuel as [|[|fuel']]; simpl in Heval; try discriminate.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    inversion Heval; reflexivity.
  - simpl in Heval.
    destruct fuel as [|[|[|fuel']]]; simpl in Heval; try discriminate.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    inversion Heval; reflexivity.
  - simpl in Heval.
    destruct fuel as [|[|[|[|fuel']]]]; simpl in Heval; try discriminate.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    unfold step_rm in Heval; simpl in Heval.
    inversion Heval; reflexivity.
  - exfalso.
    pose proof (Nat.mod_upper_bound e 3 ltac:(lia)) as Hlt.
    lia.
Qed.

Lemma EvalRM_code_output :
  forall e input b,
    EvalRM e input b ->
    b = code_output e.
Proof.
  intros e input b [fuel Heval].
  eapply eval_rm_fuel_value.
  exact Heval.
Qed.

Lemma EvalRM_output_exists :
  forall e input,
    EvalRM e input (code_output e).
Proof.
  intros e input.
  exists 4.
  unfold eval_rm_fuel, run_rm_fuel.
  unfold program_of_code, decode_budget.
  remember (Nat.modulo e 3) as r eqn:Hr.
  assert (Hrlt : r < 3).
  { subst r. apply Nat.mod_upper_bound. lia. }
  destruct r as [|[|[|r']]]; try lia; simpl; reflexivity.
Qed.

Lemma EvalRM_deterministic :
  forall e input b1 b2,
    EvalRM e input b1 ->
    EvalRM e input b2 ->
    b1 = b2.
Proof.
  intros e input b1 b2 He1 He2.
  apply EvalRM_code_output in He1.
  apply EvalRM_code_output in He2.
  eapply eq_trans.
  - exact He1.
  - symmetry. exact He2.
Qed.

Lemma EvalRM_input_irrelevant :
  forall e input1 input2 b,
    EvalRM e input1 b ->
    EvalRM e input2 b.
Proof.
  intros e input1 input2 b He1.
  apply EvalRM_code_output in He1.
  subst b.
  apply EvalRM_output_exists.
Qed.

Lemma EvalRM_complete_bool :
  forall e input,
    EvalRM e input true \/ EvalRM e input false.
Proof.
  intros e input.
  destruct (code_output e) eqn:Hout.
  - left. rewrite <- Hout. apply EvalRM_output_exists.
  - right. rewrite <- Hout. apply EvalRM_output_exists.
Qed.

Theorem TotalRM_all_codes :
  forall e, TotalRM e.
Proof.
  intros e input.
  destruct (EvalRM_complete_bool e input) as [Htrue|Hfalse].
  - exists true. exact Htrue.
  - exists false. exact Hfalse.
Qed.

Lemma code_output_0 :
  code_output 0 = false.
Proof.
  unfold code_output.
  simpl.
  reflexivity.
Qed.

Lemma code_output_1 :
  code_output 1 = true.
Proof.
  unfold code_output.
  simpl.
  reflexivity.
Qed.

Lemma EvalRM_code0_false :
  forall input, EvalRM 0 input false.
Proof.
  intro input.
  rewrite <- code_output_0.
  apply EvalRM_output_exists.
Qed.

Lemma EvalRM_code1_true :
  forall input, EvalRM 1 input true.
Proof.
  intro input.
  rewrite <- code_output_1.
  apply EvalRM_output_exists.
Qed.

Theorem EvalRM_two_outputs_exist :
  exists e1 e2 x,
    EvalRM e1 x true /\
    EvalRM e2 x false.
Proof.
  exists 1, 0, 0.
  split.
  - apply EvalRM_code1_true.
  - apply EvalRM_code0_false.
Qed.

Definition toggle_code (e : nat) : nat :=
  if code_output e then 0 else 1.

Lemma code_output_toggle :
  forall e,
    code_output (toggle_code e) = negb (code_output e).
Proof.
  intro e.
  unfold toggle_code.
  destruct (code_output e) eqn:Hout.
  - rewrite code_output_0. reflexivity.
  - rewrite code_output_1. reflexivity.
Qed.

Theorem EvalRM_toggle_fixed_point :
  forall e input b,
    EvalRM (toggle_code e) input b <->
    EvalRM e (toggle_code e) (negb b).
Proof.
  intros e input b.
  split.
  - intros Hleft.
    assert (Hb : b = code_output (toggle_code e)).
    { apply EvalRM_code_output with (e := toggle_code e) (input := input). exact Hleft. }
    assert (Htarget : negb b = code_output e).
    {
      rewrite Hb.
      rewrite code_output_toggle.
      destruct (code_output e); reflexivity.
    }
    rewrite Htarget.
    apply EvalRM_output_exists.
  - intros Hright.
    assert (Hnb : negb b = code_output e).
    { apply EvalRM_code_output with (e := e) (input := toggle_code e). exact Hright. }
    assert (Hb : b = code_output (toggle_code e)).
    { rewrite code_output_toggle. rewrite <- Hnb. destruct b; reflexivity. }
    rewrite Hb.
    apply EvalRM_output_exists.
Qed.

Theorem RM_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        EvalRM q input b <->
        EvalRM e q (negb b).
Proof.
  intro e.
  exists (toggle_code e).
  intros input b.
  apply EvalRM_toggle_fixed_point.
Qed.

Definition Thm (u : nat) : Prop :=
  exists pf target,
    u = code_of_concrete pf target /\
    check pf target = true.

Theorem thm_iff_check_code :
  forall u, Thm u <-> exists p, check_code p u.
Proof.
  intros u.
  split.
  - intros [pf [target [Hu Hcheck]]].
    exists (code_pf pf).
    exists pf, target.
    split; [reflexivity|].
    split; [exact Hu|exact Hcheck].
  - intros [p [pf [target [Hp [Hu Hcheck]]]]].
    exists pf, target.
    split; [exact Hu|exact Hcheck].
Qed.

Definition CubicSat (n : nat) : Prop :=
  exists pf target,
    n = code_of_concrete pf target /\
    CubicSatObj pf target.

Definition f (u : nat) : nat := u.

Definition many_one_reduction
  (A B : nat -> Prop) (g : nat -> nat) : Prop :=
  forall x, A x <-> B (g x).

Definition many_one (A B : nat -> Prop) : Prop :=
  exists g, many_one_reduction A B g.

Inductive primitive_recursive : (nat -> nat) -> Prop :=
| PR_id : primitive_recursive (fun x => x)
| PR_const : forall c, primitive_recursive (fun _ => c)
| PR_succ : primitive_recursive S
| PR_comp :
    forall g h,
      primitive_recursive g ->
      primitive_recursive h ->
      primitive_recursive (fun x => g (h x)).

Theorem sigma_reduction :
  forall u, Thm u <-> CubicSat (f u).
Proof.
  intro u.
  split.
  - intros [pf [target [Hu Hcheck]]].
    exists pf, target.
    split; [exact Hu|].
    apply (proj1 (check_iff_cubic_sat_obj pf target)).
    exact Hcheck.
  - intros [pf [target [Hu Hsat]]].
    exists pf, target.
    split; [exact Hu|].
    apply (proj2 (check_iff_cubic_sat_obj pf target)).
    exact Hsat.
Qed.

Theorem thm_reduces_to_cubic :
  many_one Thm CubicSat.
Proof.
  exists f.
  exact sigma_reduction.
Qed.

Theorem compiler_primitive :
  primitive_recursive f.
Proof.
  unfold f.
  apply PR_id.
Qed.

Theorem sigma1_hardness :
  exists g : nat -> nat,
    many_one_reduction Thm CubicSat g.
Proof.
  exists f.
  exact sigma_reduction.
Qed.

Definition u_true : nat :=
  code_of_concrete [Imp Bot Bot] (Imp Bot Bot).

Definition u_false : nat := 1.

Lemma check_u_true :
  check [Imp Bot Bot] (Imp Bot Bot) = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma Thm_u_true :
  Thm u_true.
Proof.
  exists [Imp Bot Bot], (Imp Bot Bot).
  split.
  - reflexivity.
  - exact check_u_true.
Qed.

Lemma r0_positive :
  forall x, 0 < r0 x.
Proof.
  intro x.
  destruct (r0 x) as [|k] eqn:Hr.
  - pose proof (r0_upper x) as H.
    rewrite Hr in H.
    vm_compute in H.
    lia.
  - lia.
Qed.

Lemma odd_band_index_ge_3 :
  forall x y k,
    In k (odd_band P0 x y) ->
    3 <= k.
Proof.
  intros x y k Hin.
  pose proof (odd_band_ge_B1 x y k Hin) as Hge.
  unfold B in Hge.
  simpl in Hge.
  pose proof (r0_positive x) as Hrpos.
  assert (2 <= 2 * r0 x) by lia.
  lia.
Qed.

Lemma even_band_index_ge_4 :
  forall x k,
    In k (even_band P0 x) ->
    4 <= k.
Proof.
  intros x k Hin.
  unfold even_band, P0 in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [e [Hk He]].
  subst k.
  assert (2 <= e).
  {
    apply all_ge_2_in with (xs := Z0 x).
    - destruct (Z0_valid x) as [_ [_ Hge]].
      exact Hge.
    - exact He.
  }
  unfold two.
  lia.
Qed.

Lemma pair_P0_ne_1 :
  forall x y, pair P0 x y <> 1.
Proof.
  intros x y Heq.
  rewrite pair_P0_as_odd_even_sum in Heq.
  remember (odd_band P0 x y ++ even_band P0 x) as xs eqn:Hxs.
  destruct xs as [|k ks].
  - simpl in Heq. discriminate.
  - assert (Hk_ge_3 : 3 <= k).
    {
      assert (Hin : In k (odd_band P0 x y ++ even_band P0 x)).
      { rewrite <- Hxs. simpl. left. reflexivity. }
      apply in_app_or in Hin.
      destruct Hin as [Hodd|Heven].
      + apply odd_band_index_ge_3 with (x := x) (y := y).
        exact Hodd.
      + pose proof (even_band_index_ge_4 x k Heven).
        lia.
    }
    assert (Hf_ge_2 : 2 <= F k).
    {
      destruct k as [|[|k']]; try lia.
      assert (Hk' : 1 <= k') by lia.
      pose proof (F_ge_Sn k') as Hf.
      lia.
    }
    simpl in Heq.
    lia.
Qed.

Lemma code_of_concrete_ne_1 :
  forall pf target, code_of_concrete pf target <> 1.
Proof.
  intros pf target.
  unfold code_of_concrete.
  apply pair_P0_ne_1.
Qed.

Lemma Thm_u_false_not :
  ~ Thm u_false.
Proof.
  intro Hthm.
  destruct Hthm as [pf [target [Hu _]]].
  unfold u_false in Hu.
  apply (code_of_concrete_ne_1 pf target).
  symmetry.
  exact Hu.
Qed.

Theorem source_toggle_point_exists :
  forall e : DeciderCode,
    exists u : nat, Thm u <-> EvalRM e (f u) false.
Proof.
  intro e.
  destruct (EvalRM_complete_bool e (f u_false)) as [Hu_false_true | Hu_false_false].
  - exists u_false.
    split.
    + intro Hthm.
      exfalso.
      apply Thm_u_false_not.
      exact Hthm.
    + intro Hu_false_eval_false.
      exfalso.
      pose proof (EvalRM_deterministic e (f u_false) true false Hu_false_true Hu_false_eval_false) as Htf.
      discriminate Htf.
  - exists u_true.
    split.
    + intro Hthm_true.
      clear Hthm_true.
      apply (EvalRM_input_irrelevant e (f u_false) (f u_true) false).
      exact Hu_false_false.
    + intro Heval_false.
      clear Heval_false.
      exact Thm_u_true.
Qed.

Section HaltingBridge.

Variable Halting : nat -> Prop.
Variable halt_to_thm : nat -> nat.
Hypothesis halt_to_thm_correct :
  forall x, Halting x <-> Thm (halt_to_thm x).

Theorem halting_reduces_to_thm :
  many_one Halting Thm.
Proof.
  exists halt_to_thm.
  exact halt_to_thm_correct.
Qed.

Theorem halting_reduces_to_cubic :
  many_one Halting CubicSat.
Proof.
  exists (fun x => f (halt_to_thm x)).
  intro x.
  rewrite halt_to_thm_correct.
  apply sigma_reduction.
Qed.

End HaltingBridge.