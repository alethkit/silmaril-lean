module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Uniformity.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Descent.Thms

/-! A literal native square maps two distinct source loop replies to unit.
Both source and target contain a protected nested dispatcher. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.Semantics
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches SubstitutionEquiv)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBPaperUniformityRegression

private abbrev τ := Ty Empty
private abbrev U : τ := .unit
private abbrev A : τ := .coprod U U
private abbrev Choice : τ := .coprod U (.coprod U U)

local instance : HasTy Unit τ := ⟨fun _ => U, fun _ => Choice⟩

private abbrev fixture : Shape.Model Unit ([] : List τ) where
  raw := {
    α := Unit
    σ := Nat
    instr := fun _ a s v t => a = .unit ∧
      (v = .inl .unit ∨ v = .inr (.inl .unit) ∨ v = .inr (.inr .unit)) ∧ t = s + 1
    faults := fun _ a s t => a = .unit ∧ t = s + 2
    prim := fun _ a _ => a = .unit
    bound := Fin.elim0 }
  atomType := fun _ _ => False
  boundTyped i := Fin.elim0 i
  instrTyped := by
    rintro _ _ _ _ _ _ ⟨_, rfl | rfl | rfl, _⟩
    · exact .inl .unit
    · exact .inr (.inl .unit)
    · exact .inr (.inr .unit)

private abbrev Raw := LambdaSSA.Region Unit
private abbrev entry : Raw := .br 0 (.inl .unit)

private abbrev dispatch (left right : LambdaSSA.Tm Unit) : Raw :=
  .let₁ (.op () .unit)
    (.case (.var 0) (.br 1 left) (.case (.var 0) (.br 1 right) (.br 2 .unit)))

private abbrev protect (r : Raw) : Raw := .cfg (.br 0 .unit) 1 (fun _ => r)

private abbrev p : Raw := protect (dispatch (.inl .unit) (.inr .unit))
private abbrev bareTarget : Raw := protect (dispatch .unit .unit)
private abbrev q : Raw := .let₁ .unit bareTarget

private theorem he : ValueBranches ([] : List τ) entry [A, U] :=
  .br (ℓ := 0) rfl (.inl .unit)

private theorem hp : ValueBranches [A] p [A, U] :=
  .cfg (fun _ : Fin 1 => U) (.br (ℓ := 0) rfl .unit) (fun _ =>
    .let₁ (.op (f := ()) .unit)
      (.case (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.inl .unit))
        (.case (.var (i := 0) rfl) (.br (ℓ := 1) rfl (.inr .unit)) (.br (ℓ := 2) rfl .unit))))

private theorem bareTargetTyped (Γ : List τ) : ValueBranches Γ bareTarget [U, U] :=
  .cfg (fun _ : Fin 1 => U) (.br (ℓ := 0) rfl .unit) (fun _ =>
    .let₁ (.op (f := ()) .unit)
      (.case (.var (i := 0) rfl) (.br (ℓ := 1) rfl .unit)
        (.case (.var (i := 0) rfl) (.br (ℓ := 1) rfl .unit) (.br (ℓ := 2) rfl .unit))))

private theorem hq : q.HasType [U] [U, U] := .let₁ .unit (bareTargetTyped [U, U]).hasType
private theorem ha : LambdaSSA.Tm.BranchValue [A] (.unit : LambdaSSA.Tm Unit) U := .unit

private theorem squareSyntax : SubstitutionEquiv [A] (squareLeft hp ha).val (squareRight hq ha).val [U, U] :=
  (SubstitutionEquiv.letValue .unit (bareTargetTyped [U, A]).hasType).symm

private abbrev source : LambdaSSA.UB.Typed (Φ := Unit) [] [U] := uniformSource he hp
private abbrev target : LambdaSSA.UB.Typed (Φ := Unit) [] [U] := uniformTarget he hq ha

private theorem installed : LambdaSSA.Region.Paper.Eqv ([] : List τ) source.val target.val [U] :=
  .uniform he hp hq ha (.cfgEta (.native squareSyntax))

private theorem same :
    Shape.denote (.native source) fixture 0 = Shape.denote (.native target) fixture 0 :=
  uniform_native_square he hp hq ha squareSyntax fixture 0

private abbrev captured := envOfBound fixture.raw.bound
private abbrev blocked := extend captured (Value.unit : Value Unit)
private abbrev targetSyntax : Raw := .cfg (.br 0 .unit) 1 (fun _ => q)

private theorem outward_return :
    (Shape.denote (.native source) fixture 0).Ordinary (.ret (0 : Fin 1) .unit 1) := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Eval fixture.raw.instr captured targetSyntax 0 0 .unit 1
  have leaving : Region.Eval fixture.raw.instr blocked q 0 1 .unit 1 :=
    .let₁ .unit (.cfg (.br .unit) (.step (by decide)
      (.let₁ (.op .unit ⟨rfl, .inr (.inr rfl), rfl⟩) (.case_inr .var (.case_inr .var (.br .unit))))
      (.exit (by decide))))
  exact .cfg (.br .unit) (.step (by decide) leaving (.exit (by decide)))

private theorem can_fault : (Shape.denote (.native source) fixture 0).Ordinary (.fault 2) := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Fault fixture.raw.instr fixture.raw.faults captured targetSyntax 0 2
  exact .cfg_follow (.br .unit) (.body (by decide)
    (.let₁_body .unit (.cfg_follow (.br .unit) (.body (by decide) (.let₁_arg (.op_fault .unit ⟨rfl, rfl⟩))))))

private theorem primitive_divergence : (Shape.denote (.native source) fixture 0).Ordinary .diverge := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region captured targetSyntax 0)
  apply External.Diverges.fold_core
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  apply External.Diverges.fold_core
  refine .follow_body (by decide) ?_
  apply External.Diverges.fold_core
  apply DivergenceStep.let₁ Tm.Eval.unit
  apply External.Diverges.fold_core
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  apply External.Diverges.fold_core
  exact .follow_body (by decide) (.fold (.let₁_arg (.primitive .unit rfl)))

private theorem replay (s : Nat) : Region.Eval fixture.raw.instr blocked q s 0 .unit (s + 1) :=
  .let₁ .unit (.cfg (.br .unit) (.step (by decide)
    (.let₁ (.op .unit ⟨rfl, .inl rfl, rfl⟩) (.case_inl .var (.br .unit))) (.exit (by decide))))

private theorem internal_replay : (Shape.denote (.native source) fixture 0).Ordinary .diverge := by
  rw [same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change External.Diverges fixture.raw.instr fixture.raw.prim (.region captured targetSyntax 0)
  apply External.Diverges.of_internal
  apply Diverges.fold
  apply DivergenceStep.cfg_follow (Region.Eval.br Tm.Eval.unit)
  refine Diverges.coinduct (fun c => ∃ s, c = .follow captured (fun _ : Fin 1 => q) 0 .unit s) ?_ ⟨0, rfl⟩
  rintro _ ⟨s, rfl⟩
  exact .follow_next (by decide) (replay s) ⟨s + 1, rfl⟩

-- This square uses the installed Paper product rule under symmetry.
private abbrev paperBody : Raw := .let₂ (.pair .unit .unit) bareTarget

private theorem paperBodyTyped : paperBody.HasType [U] [U, U] :=
  .let₂ (.pair .unit .unit) (bareTargetTyped [U, U, U]).hasType

private abbrev paperTarget : LambdaSSA.UB.Typed (Φ := Unit) [] [U] :=
  uniformTarget he paperBodyTyped ha

private theorem paperSquare : LambdaSSA.Region.Paper.Eqv [A]
    (squareLeft hp ha).val (squareRight paperBodyTyped ha).val [U, U] :=
  (LambdaSSA.Region.Paper.Eqv.productBeta (.let₂Beta .unit .unit (bareTargetTyped [U, U, A]).hasType)).symm

private theorem paperUniform : LambdaSSA.Region.Paper.Eqv ([] : List τ) source.val paperTarget.val [U] :=
  .uniform he hp paperBodyTyped ha paperSquare

private theorem paperUniform_return :
    (Shape.denote (.native paperTarget) fixture 0).Ordinary (.ret (0 : Fin 1) .unit 1) := by
  rw [← eqv_denote paperUniform fixture 0]
  exact outward_return

private theorem paperUniform_fault :
    (Shape.denote (.native paperTarget) fixture 0).Ordinary (.fault 2) := by
  rw [← eqv_denote paperUniform fixture 0]
  exact can_fault

private theorem paperUniform_diverge :
    (Shape.denote (.native paperTarget) fixture 0).Ordinary .diverge := by
  rw [← eqv_denote paperUniform fixture 0]
  exact internal_replay

-- CFG eta can sequence an effectful continuation after a successful CFG exit.
private abbrev post : Nat → Raw := fun _ => .let₁ (.op () .unit) (.br 0 .unit)

private theorem etaPost : LambdaSSA.Region.Paper.Eqv ([] : List τ)
    (source.val.lsubst post) ((entry.lsubst (LambdaSSA.Region.CfgEta.reentry p)).lsubst post) [U] :=
  .cfgEta (.etaPost he hp (fun _ _ _ => .let₁ (.op (f := ()) .unit) (.br (ℓ := 0) rfl .unit)))

private theorem etaPost_shaped (s : Nat) :
    Shape.denote (.native ⟨source.val.lsubst post, etaPost.typed.1⟩) fixture s =
      Shape.denote (.native ⟨_, etaPost.typed.2⟩) fixture s :=
  eqv_denote etaPost fixture s

private theorem etaPost_return :
    (Shape.denote (.native ⟨_, etaPost.typed.2⟩) fixture 0).Ordinary (.ret (0 : Fin 1) .unit 2) := by
  rw [← etaPost_shaped 0]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  change Region.Eval fixture.raw.instr captured (source.val.lsubst post) 0 0 .unit 2
  exact .cfg (.br (.inl .unit)) (.step (by decide)
    (.cfg (.br .unit) (.step (by decide)
      (.let₁ (.op .unit ⟨rfl, .inr (.inr rfl), rfl⟩)
        (.case_inr .var (.case_inr .var (.let₁ (.op .unit ⟨rfl, .inl rfl, rfl⟩) (.br .unit)))))
      (.exit (by decide))))
    (.exit (by decide)))

#print axioms eqv_denote
#print axioms familyDenotation_eq
#print axioms denote_mk
#print axioms paperUniform_return
#print axioms paperUniform_fault
#print axioms paperUniform_diverge
#print axioms etaPost_shaped
#print axioms etaPost_return

#print axioms uniform_of_observed_square
#print axioms uniform_native_square
#print axioms guarded_forwarding_eval
#print axioms guarded_forwarding_fault
#print axioms guarded_forwarding_diverges
#print axioms installed
#print axioms outward_return
#print axioms can_fault
#print axioms primitive_divergence
#print axioms internal_replay

end LambdaSSAUBPaperUniformityRegression
