module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Continuation.Thms

/-! A primitive can return either sum tag. One tag loops through a rewritten
CFG block and the other exits. The primitive can also fault. -/

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA (Tm)
open Silmaril.Isotope.LambdaSSA.Region
  (ContinuationFamily ContinuationHom continuationSetoid ValueBranches SubstitutionEquiv)
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

namespace LambdaSSAUBShapeContinuationRegression

private abbrev τ := Ty Empty
private abbrev U : τ := .unit
private abbrev S : τ := .coprod U U

local instance : HasTy Unit τ := ⟨fun _ => U, fun _ => S⟩

private abbrev fixture : Shape.Model Unit [U] where
  raw := {
    α := Unit
    σ := Nat
    instr := fun _ a s v t => a = .unit ∧ (v = .inl .unit ∨ v = .inr .unit) ∧ t = s + 1
    faults := fun _ a s t => a = .unit ∧ t = s + 2
    prim := fun _ _ _ => False
    bound := fun _ => .unit }
  atomType := fun _ _ => False
  boundTyped i := Fin.eq_zero i ▸ .unit
  instrTyped := by
    rintro _ _ _ _ _ _ ⟨_, h | h, _⟩
    · subst h; exact .inl .unit
    · subst h; exact .inr .unit

private abbrev Region := LambdaSSA.Region Unit
private abbrev body : Region := .case (.var 0) (.br 0 (.inl (.var 0))) (.br 1 .unit)
private abbrev expanded : Region :=
  .case (.var 0) (body.substVars (Tm.replaceNewest (.inl (.var 0))))
    (body.substVars (Tm.replaceNewest (.inr (.var 0))))

private theorem typedBody (Γ : List τ) : ValueBranches (S :: Γ) body [S, U] :=
  .case (.var (i := 0) rfl)
    (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) (.br (ℓ := 1) rfl .unit)

private theorem blockRewrite : SubstitutionEquiv [S, U] expanded body [S, U] :=
  .caseValue (.var (i := 0) rfl) (typedBody [S, U]).hasType

-- The entry first binds the primitive's reply, making its branch argument a value.
private abbrev bindingEntry : Region := .let₁ (.op () .unit) (.br 0 (.var 0))

private theorem typedBindingEntry : ValueBranches [U] bindingEntry [S, U] :=
  .let₁ (.op (f := ()) .unit) (.br (ℓ := 0) rfl (.var (i := 0) rfl))

private abbrev loop (block : Region) : Region := .cfg bindingEntry 1 (fun _ => block)

private theorem loopRewrite : SubstitutionEquiv [U] (loop expanded) (loop body) [U] :=
  .cfg (fun _ => S) (.base (.refl typedBindingEntry.hasType)) (fun _ => blockRewrite)

private theorem expandedTyped : ValueBranches [S, U] expanded [S, U] := by
  exact .case (.var (i := 0) rfl)
    (.case (.inl (B := U) (.var (i := 0) rfl))
      (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) (.br (ℓ := 1) rfl .unit))
    (.case (.inr (A := U) (.var (i := 0) rfl))
      (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl))) (.br (ℓ := 1) rfl .unit))

private def family {r : Region} (hr : ValueBranches [U] r [U]) :
    ContinuationFamily (Φ := Unit) [] [U] [U] :=
  ⟨fun _ => r, fun _ _ here => (List.mem_singleton.mp (List.mem_of_getElem? here)) ▸ hr⟩

private noncomputable abbrev quotientDenotes (block : Region) (typed : ValueBranches [S, U] block [S, U]) :
    Behaviour 1 Unit Nat :=
  let f := family (.cfg (fun _ : Fin 1 => S) typedBindingEntry (fun _ => typed))
  Shape.Continuation.denote (Quotient.mk (continuationSetoid [] [U] [U]) f) 0 fixture 0

private theorem denote_same :
    quotientDenotes expanded expandedTyped = quotientDenotes body (typedBody [U]) := by
  apply congrArg (fun (q : ContinuationHom (Φ := Unit) [] [U] [U]) => Shape.Continuation.denote q 0 fixture 0)
  apply Quotient.sound
  intro i A here
  have hA : A = U := List.mem_singleton.mp (List.mem_of_getElem? here)
  subst A
  exact loopRewrite

private abbrev runtimeEnv : Env Unit := envOfBound fixture.raw.bound

private theorem enter_left :
    LambdaSSA.Semantics.Region.Eval fixture.raw.instr runtimeEnv bindingEntry 0 0 (.inl .unit) 1 :=
  .let₁ (.op .unit ⟨rfl, .inl rfl, rfl⟩) (.br .var)

private theorem enter_right :
    LambdaSSA.Semantics.Region.Eval fixture.raw.instr runtimeEnv bindingEntry 0 0 (.inr .unit) 1 :=
  .let₁ (.op .unit ⟨rfl, .inr rfl, rfl⟩) (.br .var)

private theorem can_return :
    (quotientDenotes expanded expandedTyped).Ordinary (.ret 0 .unit 1) := by
  rw [denote_same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  exact LambdaSSA.Semantics.Region.Eval.cfg enter_right
    (.step (by decide) (.case_inr .var (.br .unit)) (.exit (by decide)))

private theorem can_fault :
    (quotientDenotes expanded expandedTyped).Ordinary (.fault 2) := by
  rw [denote_same]
  exact ⟨WithTop.coe_ne_top, LambdaSSA.Semantics.Region.Fault.cfg_entry (.let₁_arg (.op_fault .unit ⟨rfl, rfl⟩))⟩

private theorem can_replay :
    (quotientDenotes expanded expandedTyped).Ordinary .diverge := by
  rw [denote_same]
  refine ⟨WithTop.coe_ne_top, ?_⟩
  apply LambdaSSA.Semantics.External.Diverges.fold_core
  apply LambdaSSA.Semantics.DivergenceStep.cfg_follow enter_left
  refine LambdaSSA.Semantics.External.Diverges.coinduct
    (fun c => c = .follow runtimeEnv (fun _ : Fin 1 => body) 0 (.inl .unit) 1) ?_ rfl
  rintro c rfl
  exact .core (.follow_next (by decide) (.case_inl .var (.br (.inl .var))) rfl)

#print axioms Shape.Continuation.substitutionEquiv_denote
#print axioms Shape.Continuation.denote
#print axioms denote_same
#print axioms can_return
#print axioms can_fault
#print axioms can_replay

end LambdaSSAUBShapeContinuationRegression
