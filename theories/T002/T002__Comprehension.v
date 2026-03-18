(* T002__Comprehension.v *)

From Coq Require Import Bool List.
Import ListNotations.

From T002 Require Import
  R01__Foundation_Fibonacci
  R02__Foundation_Zeckendorf
  R04__Verification_Hilbert_Syntax
  R05__Verification_Hilbert_Checker
  R08__Constraints_Axiom
  R11__Constraints_Assembly
  R13__Kernel_API
  R15__Code_Bridge
  R18__Sigma_Reduction_API
  R21__Pairing_Correctness_P0
  R22__Channel_Bounds
  P00__Concrete_Provability
  P00__Provability_Interface
  P01__HBL
  P02__Diagonal
  P03__Undecidability
  P04__RA_Certification
  P05__Toggle_Contradiction
  P06__SourceToggle_Generator.

(*************************************************************************)
(*                                   .                                   *)
(*                                  ___                                  *)
(*                       `  .    .'     `.     .  ´                      *)
(*                              /         \                              *)
(*                             |           |                             *)
(*                     _  .    |           |    .  _                     *)
(*                              .  :~~~:  .                              *)
(*                               `. \ / .'                               *)
(*                           .     |_|_|     .                           *)
(*                          ´      (===)      `                          *)
(*                                  `-´                                  *)
(*                                                                       *)
(*    Proofcase / T002 -- Comprehension Layer                            *)
(*                                                                       *)
(*    This file serves as a proof-semantic synopsis and comprehension    *)
(*    aid for project T002. It introduces no new constructive content    *)
(*    or  derivations; but consolidates the core semantics (theorems,    *)
(*    lemmas,  and corollaries, together with their endpoints) into a    *)
(*    unified structure for readability and auditability.                *)
(*                                                                       *)
(*************************************************************************)

Section Proof_Index.

(*
  Overview
  --------

  `T002` splits into three audit-facing tiers.

  (i) TIER 1: CERTIFIED COMPILATION

      (a) An executable Hilbert checker is exposed through a cubic-kernel
          interface: proof/target pairs are compiled into a bounded-degree
          polynomial system and then into one aggregated cubic equation.

      (b) A code bridge packages concrete proof objects as natural numbers,
          after which `R18` exposes the stable reduction API
          `Thm u <-> CubicSat (f u)`.

  (ii) TIER 2: FIXED-POINT LOGIC

      (a) `P00__Concrete_Provability` supplies the coded proof predicate and
          the substitution-code substrate.

      (b) `P02__Diagonal` is the genuine comprehension branch:
          templates, closed-code substitution, and the fixed-point theorem.

      (c) `P01__HBL` exports the derivability conditions and the
          representability lemmas needed to read the diagonal layer as
          provability semantics.

      (d) `P00__Provability_Interface`, `P06`, `P05`, and `P03` form the
          endpoint branch: source toggle points are turned into cubic toggle
          witnesses, and these collapse every supposedly correct coded decider.

  (iii) TIER 3: INTERNAL CERTIFICATION COROLLARY

      (a) `P04__RA_Certification` is a section-parametric corollary:
          any ambient certification predicate that implies `CorrectCode`
          is already impossible by Tier 2.
*)

(*************************************************************************)
(*                                                                       *)
(*                     TIER 1: CERTIFIED COMPILATION                     *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  KERNEL AND SINGLE-CUBIC SURFACE
*)

(*
  (1)
  Core syntax of target formulas.
*)

Definition audit_form : Type :=
  Form.

(*
  (2)
  Proof objects checked by the executable Hilbert kernel.
*)

Definition audit_proof : Type :=
  Proof.

(*
  (3)
  Assignment type used by the polynomial semantics.
*)

Definition audit_assignment : Type :=
  Assignment.

(*
  (4)
  Polynomial carrier used by the cubic compilation layer.
*)

Definition audit_polynomial : Type :=
  Polynomial.

(*
  (5)
  Public checker alias for concrete proof verification.
*)

Definition audit_checker : audit_proof -> audit_form -> bool :=
  checker.

(*
  (6)
  Audit-facing name for the kernel acceptance predicate after the cubic
  interface boundary.
*)

Definition audit_cubic_accepts : audit_proof -> audit_form -> bool :=
  cubic_accepts.

(*
  (7)
  Canonical assignment extracted from a proof/target pair for system emission.
*)

Definition audit_canonical_assignment :
  audit_proof -> audit_form -> audit_assignment :=
  canonical_assignment.

(*
  (8)
  Emitted finite polynomial system attached to a proof and target formula.
*)

Definition audit_emit_cubic_system :
  audit_proof -> audit_form -> list audit_polynomial :=
  emit_cubic_system.

(*
  (9)
  Aggregated single-equation cubic certificate for the emitted system.
*)

Definition audit_emit_single_cubic :
  audit_proof -> audit_form -> audit_polynomial * audit_polynomial :=
  emit_single_cubic.

(*
  (10)
  Compiler surface for the finite list of cubic constraints.
*)

Definition audit_compile :
  audit_proof -> audit_form -> list audit_polynomial :=
  compile.

(*
  (11)
  Semantic zero predicate for every polynomial in a compiled system.
*)

Definition audit_all_zero :
  list audit_polynomial -> audit_assignment -> Prop :=
  all_zero.

(*
  (12)
  Semantic equality predicate for the single aggregated cubic equation.
*)

Definition audit_equation_holds :
  audit_polynomial * audit_polynomial -> audit_assignment -> Prop :=
  equation_holds.

(*
  (13)
  Existence of a witness assignment solving the single cubic equation attached
  to a concrete proof instance.
*)

Definition audit_cubic_witness :
  audit_proof -> audit_form -> Prop :=
  CubicWitness.

(*
  (14)
  Carryless pairing correctness for the distinguished `P0` instance used by
  concrete coding and by the diagonal layer.
*)

Definition audit_unpair_pair_P0 :
  forall x y,
    unpair P0 (pair P0 x y) = (x, y) :=
  unpair_pair_P0.

(*
  (15)
  Main kernel-correctness theorem at the single-cubic boundary.
*)

Definition audit_cubic_accepts_iff_cubic_witness :
  forall pf target,
    audit_cubic_accepts pf target = true <->
    audit_cubic_witness pf target :=
  cubic_accepts_iff_cubic_witness.

(*
  (16)
  Stronger system-level correctness theorem:
  checker acceptance is equivalent to a zero assignment for the compiled finite
  cubic system.
*)

Definition audit_check_iff_emit_cubic_all_zero :
  forall pf target,
    audit_checker pf target = true <->
    exists a,
      as_pf a = pf /\
      as_target a = target /\
      audit_all_zero (audit_emit_cubic_system pf target) a :=
  check_iff_emit_cubic_all_zero.

(*
  (17)
  Every emitted polynomial in the compiled system has total degree at most `3`.
*)

Definition audit_degree_three_threshold :
  forall pf target,
    Forall (fun P => total_degree P <= 3)
           (audit_compile pf target) :=
  R13__Kernel_API.degree_three_threshold.

(*
  (18)
  Degree certification for the two sides of the single aggregated cubic
  equation.
*)

Definition audit_emit_single_cubic_degree_le_3 :
  forall pf target,
    total_degree (fst (audit_emit_single_cubic pf target)) <= 3 /\
    total_degree (snd (audit_emit_single_cubic pf target)) <= 3 :=
  emit_single_cubic_degree_le_3.

(*
  (19)
  Explicit aggregated evaluator for the single cubic equation.
*)

Definition audit_eval_agg :
  audit_proof -> audit_form -> audit_assignment -> nat :=
  eval_agg.

(*
  (20)
  Satisfaction predicate phrased directly in terms of the aggregated evaluator.
*)

Definition audit_agg_sat :
  audit_proof -> audit_form -> Prop :=
  AggSat.

(*
  (21)
  Uniform channel bound needed by the aggregated-evaluator presentation.
*)

Definition audit_channel_bound_M : nat :=
  channel_bound_M.

(*
  (22)
  Aggregated evaluator correctness:
  once the base exceeds the certified channel bound, the single cubic witness
  semantics and the explicit evaluator semantics coincide.
*)

Definition audit_aggregation_correct :
  forall base pf target,
    base > audit_channel_bound_M ->
    audit_cubic_witness pf target <-> audit_agg_sat pf target :=
  aggregation_correct.

(*
  (ii)
  CODE BRIDGE AND MANY-ONE REDUCTION
*)

(*
  (1)
  Coding of closed formulas into naturals at the bridge layer.
*)

Definition audit_enc_form_nat : audit_form -> nat :=
  enc_form_nat.

(*
  (2)
  Coding of proof traces as naturals.
*)

Definition audit_code_pf : audit_proof -> nat :=
  code_pf.

(*
  (3)
  Coding of a concrete `(proof, target)` instance as one natural.
*)

Definition audit_code_of_concrete :
  audit_proof -> audit_form -> nat :=
  code_of_concrete.

(*
  (4)
  Coded checker acceptance relation.
*)

Definition audit_check_code : nat -> nat -> Prop :=
  check_code.

(*
  (5)
  Source theoremhood predicate used by the reduction endpoint.
*)

Definition audit_thm : nat -> Prop :=
  R18__Sigma_Reduction_API.Thm.

(*
  (6)
  Target cubic satisfiability predicate on codes.
*)

Definition audit_cubic_sat : nat -> Prop :=
  R18__Sigma_Reduction_API.CubicSat.

(*
  (7)
  Reduction map sending theorem codes to cubic-instance codes.
*)

Definition audit_reduction_map : nat -> nat :=
  R18__Sigma_Reduction_API.f.

(*
  (8)
  Standard many-one reduction predicate.
*)

Definition audit_many_one_reduction
  (A B : nat -> Prop) (g : nat -> nat) : Prop :=
  R18__Sigma_Reduction_API.many_one_reduction A B g.

(*
  (9)
  Existential many-one reducibility predicate.
*)

Definition audit_many_one (A B : nat -> Prop) : Prop :=
  R18__Sigma_Reduction_API.many_one A B.

(*
  (10)
  Primitive-recursive compiler predicate used to qualify `f`.
*)

Definition audit_primitive_recursive : (nat -> nat) -> Prop :=
  R18__Sigma_Reduction_API.primitive_recursive.

(*
  (11)
  Coded decider type at the reduction layer.
*)

Definition audit_rm_decider_code : Type :=
  R18__Sigma_Reduction_API.DeciderCode.

(*
  (12)
  Execution semantics for coded deciders.
*)

Definition audit_eval_rm :
  audit_rm_decider_code -> nat -> bool -> Prop :=
  R18__Sigma_Reduction_API.EvalRM.

(*
  (13)
  Totality predicate for coded deciders.
*)

Definition audit_total_rm :
  audit_rm_decider_code -> Prop :=
  R18__Sigma_Reduction_API.TotalRM.

(*
  (14)
  Toggle transformation on decider codes.
*)

Definition audit_toggle_code :
  audit_rm_decider_code -> audit_rm_decider_code :=
  R18__Sigma_Reduction_API.toggle_code.

(*
  (15)
  Certified reduction endpoint:
  theoremhood on the source side is equivalent to cubic satisfiability on the
  image of the compiler.
*)

Definition audit_sigma_reduction :
  forall u,
    audit_thm u <-> audit_cubic_sat (audit_reduction_map u) :=
  sigma_reduction.

(*
  (16)
  Semantic unpacking of the target predicate:
  a coded cubic instance is satisfiable exactly when it comes from a concrete
  proof/target pair whose aggregated evaluator returns `0`.
*)

Definition audit_cubic_sat_semantic :
  forall n,
    audit_cubic_sat n <->
    exists pf target a,
      n = audit_code_of_concrete pf target /\
      as_pf a = pf /\
      as_target a = target /\
      audit_eval_agg pf target a = 0 :=
  R18__Sigma_Reduction_API.CubicSat_semantic.

(*
  (17)
  The source predicate is precisely coded checker acceptance.
*)

Definition audit_thm_iff_check_code :
  forall u,
    audit_thm u <-> exists p, audit_check_code p u :=
  thm_iff_check_code.

(*
  (18)
  Many-one reducibility of theoremhood to cubic satisfiability.
*)

Definition audit_thm_reduces_to_cubic :
  audit_many_one audit_thm audit_cubic_sat :=
  thm_reduces_to_cubic.

(*
  (19)
  Primitive-recursive status of the compiler.
*)

Definition audit_compiler_primitive :
  audit_primitive_recursive audit_reduction_map :=
  compiler_primitive.

(*
  (20)
  Explicit witness to the Sigma_1-hardness reduction.
*)

Definition audit_sigma1_hardness :
  exists g : nat -> nat,
    audit_many_one_reduction audit_thm audit_cubic_sat g :=
  sigma1_hardness.

(*
  (21)
  Abstract transport from any halting predicate that already reduces to
  theoremhood.
*)

Definition audit_halting_reduces_to_thm :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> audit_thm (halt_to_thm x)) ->
    audit_many_one Halting audit_thm :=
  halting_reduces_to_thm.

(*
  (22)
  Composition of the previous transport with the cubic reduction.
*)

Definition audit_halting_reduces_to_cubic :
  forall (Halting : nat -> Prop) (halt_to_thm : nat -> nat),
    (forall x, Halting x <-> audit_thm (halt_to_thm x)) ->
    audit_many_one Halting audit_cubic_sat :=
  halting_reduces_to_cubic.

(*
  (23)
  Determinism of coded evaluation.
*)

Definition audit_eval_rm_deterministic :
  forall e input b1 b2,
    audit_eval_rm e input b1 ->
    audit_eval_rm e input b2 ->
    b1 = b2 :=
  eval_rm_deterministic.

(*
  (24)
  Total coded deciders always produce some output.
*)

Definition audit_eval_rm_total :
  forall e input,
    audit_total_rm e ->
    exists b, audit_eval_rm e input b :=
  eval_rm_total.

(*
  (25)
  Fixed-point toggle law for coded evaluation.
*)

Definition audit_eval_rm_toggle_fixed_point :
  forall e input b,
    audit_eval_rm (audit_toggle_code e) input b <->
    audit_eval_rm e (audit_toggle_code e) (negb b) :=
  eval_rm_toggle_fixed_point.

(*
  (26)
  Recursion theorem for coded deciders.
*)

Definition audit_rm_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        audit_eval_rm q input b <->
        audit_eval_rm e q (negb b) :=
  rm_recursion_theorem.

(*
  (27)
  Tier-1 endpoint alias, phrased through provability semantics:
  theoremhood and cubic satisfiability agree on the compiler image.
*)

Definition audit_tier1_endpoint :
  forall u,
    P00__Provability_Interface.Prov u <->
    audit_cubic_sat (audit_reduction_map u) :=
  sigma_reduction_for_prov.

(*************************************************************************)
(*                                                                       *)
(*                TIER 2: FIXED-POINT LOGIC AND ENDPOINTS                *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  CONCRETE PROVABILITY AND INTERFACE
*)

(*
  (1)
  Concrete coded-proof relation: code `p` proves code `u` iff the checker
  accepts the corresponding decoded proof/target pair.
*)

Definition audit_concrete_proof : nat -> nat -> Prop :=
  Concrete_Proof.

(*
  (2)
  Existential coded provability predicate.
*)

Definition audit_prov_code : nat -> Prop :=
  ProvCode.

(*
  (3)
  Unfolding of the concrete coded-proof relation back to a genuine proof trace
  and target formula.
*)

Definition audit_concrete_proof_unfold :
  forall p u,
    audit_concrete_proof p u <->
    exists pf target,
      p = audit_code_pf pf /\
      u = audit_code_of_concrete pf target /\
      audit_checker pf target = true :=
  Concrete_Proof_unfold.

(*
  (4)
  Any accepted concrete proof yields a coded provability witness.
*)

Definition audit_checker_accepts_implies_prov_code :
  forall pf target,
    audit_checker pf target = true ->
    audit_prov_code (audit_code_of_concrete pf target) :=
  checker_accepts_implies_ProvCode.

(*
  (5)
  Open-form syntax with one distinguished hole, used by the code-level
  diagonalization layer.
*)

Definition audit_oform : Type :=
  OForm.

(*
  (6)
  Substitution operation on codes.
  The first argument is the distinguished hole code.
*)

Definition audit_subst_code : nat -> nat -> nat -> nat :=
  subst_code.

(*
  (7)
  Closed-code predicate: the code names some genuine formula.
*)

Definition audit_closed_code : nat -> Prop :=
  ClosedCode.

(*
  (8)
  Closing an open form by plugging an actual formula into the distinguished
  hole.
*)

Definition audit_close_oform :
  audit_oform -> audit_form -> audit_form :=
  close_oform.

(*
  (9)
  Correctness of the substitution-code procedure.
  The hole code and freshness assumptions remain explicit parameters.
*)

Definition audit_subst_code_correct :=
  @subst_code_correct.

(*
  (10)
  Closedness is preserved by the substitution-code procedure.
*)

Definition audit_subst_code_preserves_closed :=
  @subst_code_preserves_closed.

(*
  (11)
  Provability predicate exposed by the public proof-theory interface.
*)

Definition audit_prov : nat -> Prop :=
  P00__Provability_Interface.Prov.

(*
  (12)
  Extensional deciders on naturals.
*)

Definition audit_decider : Type :=
  P00__Provability_Interface.Decider.

(*
  (13)
  Coded deciders at the proof-theory interface.
*)

Definition audit_decider_code : Type :=
  P00__Provability_Interface.DeciderCode.

(*
  (14)
  Evaluation semantics for coded deciders at the interface boundary.
*)

Definition audit_eval_code :
  audit_decider_code -> nat -> bool -> Prop :=
  P00__Provability_Interface.EvalCode.

(*
  (15)
  Totality predicate for coded deciders.
*)

Definition audit_total_code :
  audit_decider_code -> Prop :=
  P00__Provability_Interface.TotalCode.

(*
  (16)
  Correctness predicate for coded deciders deciding the cubic target.
*)

Definition audit_correct_code :
  audit_decider_code -> Prop :=
  P00__Provability_Interface.CorrectCode.

(*
  (17)
  Extensional correctness predicate for ordinary deciders.
*)

Definition audit_correct :
  audit_decider -> Prop :=
  P00__Provability_Interface.Correct.

(*
  (18)
  Realizability of an extensional decider by some total code.
*)

Definition audit_computable :
  audit_decider -> Prop :=
  P00__Provability_Interface.Computable.

(*
  (19)
  Ordinary decidability of a predicate on naturals.
*)

Definition audit_decidable :
  (nat -> Prop) -> Prop :=
  P00__Provability_Interface.Decidable.

(*
  (20)
  Decidability witnessed directly by a total code.
*)

Definition audit_decidable_code :
  (nat -> Prop) -> Prop :=
  P00__Provability_Interface.DecidableCode.

(*
  (21)
  Interface-level determinism of coded evaluation.
*)

Definition audit_eval_code_deterministic :
  forall e input b1 b2,
    audit_eval_code e input b1 ->
    audit_eval_code e input b2 ->
    b1 = b2 :=
  EvalCode_deterministic.

(*
  (22)
  Interface-level totality theorem for coded evaluation.
*)

Definition audit_eval_code_total_input :
  forall e input,
    audit_total_code e ->
    exists b, audit_eval_code e input b :=
  EvalCode_total_input.

(*
  (23)
  Toggle fixed-point law at the interface level.
*)

Definition audit_eval_code_toggle_fixed_point :
  forall e input b,
    audit_eval_code (audit_toggle_code e) input b <->
    audit_eval_code e (audit_toggle_code e) (negb b) :=
  EvalCode_toggle_fixed_point.

(*
  (24)
  Interface-level recursion theorem.
*)

Definition audit_eval_code_recursion_theorem :
  forall e,
    exists q,
      forall input b,
        audit_eval_code q input b <->
        audit_eval_code e q (negb b) :=
  EvalCode_recursion_theorem.

(*
  (25)
  Provability and theoremhood coincide.
*)

Definition audit_prov_iff_thm :
  forall u,
    audit_prov u <-> audit_thm u :=
  Prov_iff_Thm.

(*
  (26)
  Reduction endpoint rewritten with the provability predicate on the source
  side.
*)

Definition audit_sigma_reduction_for_prov :
  forall u,
    audit_prov u <-> audit_cubic_sat (audit_reduction_map u) :=
  sigma_reduction_for_prov.

(*
  (27)
  Any computable correct decider yields a correct coded decider.
*)

Definition audit_computable_correct_implies_correct_code :
  forall D,
    audit_computable D ->
    audit_correct D ->
    exists e, audit_correct_code e :=
  computable_correct_implies_correct_code.

(*
  (ii)
  DIAGONAL / COMPREHENSION BRANCH
*)

(*
  (1)
  Sigma_1-style coded provability decomposition.
*)

Definition audit_prov_sigma1 :
  forall u,
    audit_prov_code u <-> exists p, audit_concrete_proof p u :=
  Prov_sigma1.

(*
  (2)
  Forward bridge from an accepted checker trace to coded provability.
*)

Definition audit_prov_from_check :
  forall pf target,
    audit_checker pf target = true ->
    audit_prov_code (audit_code_of_concrete pf target) :=
  Prov_from_check.

(*
  (3)
  Converse witness extraction from coded provability.
*)

Definition audit_prov_to_concrete_witness :
  forall u,
    audit_prov_code u ->
    exists p, audit_concrete_proof p u :=
  Prov_to_concrete_witness.

(*
  (4)
  First derivability clause in its concrete checker form.
*)

Definition audit_HBL_1 :
  forall pf target,
    audit_checker pf target = true ->
    audit_prov_code (audit_code_of_concrete pf target) :=
  HBL_1.

(*
  (5)
  Second derivability clause: coded provability already contains a concrete
  proof witness.
*)

Definition audit_HBL_2 :
  forall u,
    audit_prov_code u ->
    exists p, audit_concrete_proof p u :=
  HBL_2.

(*
  (6)
  Formula-level provability predicate.
*)

Definition audit_prov_formula :
  audit_form -> Prop :=
  ProvFormula.

(*
  (7)
  Internalized modus ponens on formula-level provability.
*)

Definition audit_prov_MP :
  forall (u v : audit_form),
    audit_prov_formula (Imp u v) ->
    audit_prov_formula u ->
    audit_prov_formula v :=
  Prov_MP.

(*
  (8)
  Third derivability clause, expressed via the formula-level provability
  predicate.
*)

Definition audit_HBL_3 :
  forall (u v : audit_form),
    audit_prov_formula (Imp u v) ->
    audit_prov_formula u ->
    audit_prov_formula v :=
  HBL_3.

(*
  (9)
  Open-form substitution used by the code-level diagonal construction.
*)

Definition audit_apply_oform :=
  @apply_oform.

(*
  (10)
  Template carrier for the diagonalization layer.
*)

Definition audit_template :=
  Template.

(*
  (11)
  Admissibility predicate for templates.
*)

Definition audit_template_admissible :=
  @TemplateAdmissible.

(*
  (12)
  Template application on a code.
*)

Definition audit_apply_template :=
  @apply_template.

(*
  (13)
  Canonical seed used to build a fixed point from a template.
*)

Definition audit_diagonal_seed :=
  @diagonal_seed.

(*
  (14)
  Self-unfolding law defining a fixed point for a template.
*)

Definition audit_unfold_law :=
  @UnfoldLaw.

(*
  (15)
  Extensional collapse predicate guaranteeing template self-application is
  independent of the input code.
*)

Definition audit_template_ok :=
  @TemplateOK.

(*
  (16)
  Strengthened fixed-point reading: the resulting code unfolds as a closed
  substitution instance.
*)

Definition audit_unfolds_as_closed_subst :=
  @UnfoldsAsClosedSubst.

(*
  (17)
  Parameterized fixed-point package combining closedness, self-unfolding, and
  the explicit closed-substitution reading.
*)

Definition audit_fixed_point_code_unfold :=
  @fixed_point_code_unfold.

(*
  (18)
  Diagonal endpoint:
  every admissible template has a closed fixed point.
*)

Definition audit_fixed_point :=
  @FixedPoint.

(*
  (19)
  Substitution preserves closedness at the provability-facing level.
*)

Definition audit_prov_subst :=
  Prov_subst.

(*
  (20)
  Audit-facing name for numeralwise representability of code maps.
*)

Definition audit_code_map_represents :=
  code_map_represents.

(*
  (21)
  Representation theorem for the substitution map induced by an admissible open
  formula.
*)

Definition audit_prov_representation :=
  Prov_representation.

(*
  (iii)
  TOGGLE CONTRADICTION AND IMPOSSIBILITY BRANCH
*)

(*
  (1)
  A toggle witness for a coded decider is a cubic instance whose correct
  answer is the negation of the decider output.
*)

Definition audit_toggle_witness_code :
  audit_decider_code -> Prop :=
  ToggleWitnessCode.

(*
  (2)
  Uniform generator of toggle witnesses.
*)

Definition audit_toggle_witness_code_generator : Prop :=
  ToggleWitnessCodeGenerator.

(*
  (3)
  Source-side toggle point phrased over theorem codes before transport through
  the cubic reduction.
*)

Definition audit_source_toggle_point_code :
  audit_decider_code -> nat -> Prop :=
  SourceTogglePointCode.

(*
  (4)
  Uniform source-toggle generator.
*)

Definition audit_source_toggle_code_generator : Prop :=
  SourceToggleCodeGenerator.

(*
  (5)
  Audit-facing name for the contradiction schema saying every correct coded
  decider collapses.
*)

Definition audit_toggle_instance_contradiction_code : Prop :=
  Toggle_Instance_Contradiction_Code.

(*
  (6)
  Interface-level source fixed point:
  for every coded decider there is a theorem code whose reduction image toggles
  that decider.
*)

Definition audit_source_toggle_point_exists :
  forall e : audit_decider_code,
    exists u : nat,
      audit_thm u <-> audit_eval_code e (audit_reduction_map u) false :=
  P00__Provability_Interface.source_toggle_point_exists.

(*
  (7)
  Transport of a source toggle point to a cubic toggle witness.
*)

Definition audit_toggle_witness_code_from_source_point :
  forall e u,
    audit_source_toggle_point_code e u ->
    audit_toggle_witness_code e :=
  toggle_witness_code_from_source_point.

(*
  (8)
  Uniform source-toggle generation implies uniform cubic toggle generation.
*)

Definition audit_toggle_witness_code_generator_from_source :
  audit_source_toggle_code_generator ->
  audit_toggle_witness_code_generator :=
  toggle_witness_code_generator_from_source.

(*
  (9)
  A single toggle witness for a correct code is already contradictory.
*)

Definition audit_toggle_witness_code_contradiction :
  forall e : audit_decider_code,
    audit_correct_code e ->
    audit_toggle_witness_code e ->
    False :=
  toggle_witness_code_contradiction.

(*
  (10)
  Internal generator of source toggle points from the recursion theorem and the
  source-side interface.
*)

Definition audit_source_toggle_code_generator_internal :
  audit_source_toggle_code_generator :=
  source_toggle_code_generator_internal.

(*
  (11)
  Uniform toggle witnesses collapse every correct coded decider.
*)

Definition audit_toggle_instance_contradiction_of_generator_code :
  audit_toggle_witness_code_generator ->
  audit_toggle_instance_contradiction_code :=
  toggle_instance_contradiction_of_generator_code.

(*
  (12)
  Tier-2 endpoint:
  there is no total correct coded decider for the cubic target predicate.
*)

Definition audit_no_total_correct_code_cubic_sat :
  ~ exists e : audit_decider_code, audit_correct_code e :=
  no_total_correct_code_CubicSat.

(*
  (13)
  Extensional computable deciders are equally impossible.
*)

Definition audit_no_total_correct_decider_cubic_sat_computable :
  ~ exists D : audit_decider,
      audit_computable D /\ audit_correct D :=
  no_total_correct_decider_CubicSat_computable.

(*
  (14)
  Code-level undecidability of the cubic target predicate.
*)

Definition audit_cubic_sat_undecidable_code :
  ~ audit_decidable_code audit_cubic_sat :=
  CubicSat_undecidable_code.

(*
  (15)
  Canonical Tier-2 endpoint alias for downstream audit references.
*)

Definition audit_tier2_endpoint :
  ~ exists e : audit_decider_code, audit_correct_code e :=
  no_total_correct_code_CubicSat.

(*************************************************************************)
(*                                                                       *)
(*                                  QED                                  *)
(*                                                                       *)
(*                No Total Correct Code For Single Cubics                *)
(*                                                                       *)
(*                            PROOF IN STEPS                             *)
(*                                                                       *)
(*    Step 1. Use the certified compiler to identify source-side         *)
(*            provability with cubic satisfiability on the image of      *)
(*            `audit_reduction_map`.                                     *)
(*                                                                       *)
(*    Step 2. For any coded decider `e`,                                 *)
(*            obtain a source toggle point `u` with                      *)
(*            `audit_thm u <-> audit_eval_code e (reduction_map u)       *)
(*            false`.                                                    *)
(*                                                                       *)
(*    Step 3. Transport that source toggle point through the reduction   *)
(*            interface to a cubic toggle witness.                       *)
(*                                                                       *)
(*    Step 4. Show that a correct coded decider cannot admit such a      *)
(*            toggle witness, by determinism and totality of coded       *)
(*            evaluation.                                                *)
(*                                                                       *)
(*    Step 5. Conclude that no total correct coded decider exists for    *)
(*            the cubic target predicate.                                *)
(*                                                                       *)
(*                             MECHANIZATION                             *)
(*                                                                       *)
(*         ~ exists e : audit_decider_code, audit_correct_code e         *)
(*                                                                       *)
(*                                READING                                *)
(*                                                                       *)
(*    The single-cubic target predicate exported by `T002` is not        *)
(*    decidable by any total coded decider admitted by the development.  *)
(*    The contradiction is constructive: every candidate decider can be  *)
(*    diagonalized against itself and then transported through the       *)
(*    certified cubic reduction.                                         *)
(*                                                                       *)
(*                             QUALIFICATION                             *)
(*                                                                       *)
(*    This is the main mechanized impossibility endpoint of `T002`.      *)
(*    Tier 3 adds only the section-parametric certification corollary;   *)
(*    it does not change the constructive contradiction established      *)
(*    here.                                                              *)
(*                                                                       *)
(*************************************************************************)

(*************************************************************************)
(*                                                                       *)
(*            TIER 3: INTERNAL CERTIFICATION / SECTION COROLLARY         *)
(*                                                                       *)
(*************************************************************************)

(*
  (i)
  Any ambient certification predicate implying `CorrectCode` is inconsistent
  with Tier 2. The theorem remains section-parametric in the certification
  predicate and its soundness hypothesis.
*)

Definition audit_no_RA_certified_decider_code :=
  no_RA_certified_decider_code.

(*
  (ii)
  Canonical Tier-3 endpoint alias.
*)

Definition audit_tier3_endpoint :=
  no_RA_certified_decider_code.

End Proof_Index.

Print Assumptions check_iff_emit_cubic_all_zero.
Print Assumptions sigma_reduction.
Print Assumptions FixedPoint.
Print Assumptions no_total_correct_code_CubicSat.
Print Assumptions no_RA_certified_decider_code.
