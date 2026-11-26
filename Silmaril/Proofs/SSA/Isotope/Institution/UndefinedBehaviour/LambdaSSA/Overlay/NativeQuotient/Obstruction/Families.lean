module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.NativeQuotient.Obstruction.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.Institution.Observational
open Silmaril.Isotope.Morphism.SSAIter (envOfBound)

universe u v

variable {τ : Type v} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]

private def singleton {A B : τ} {r : LambdaSSA.Region Φ} (h : ValueBranches [A] r [B]) :
    ContinuationFamily (Φ := Φ) [] [A] [B] :=
  ⟨fun _ => r, fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)) ▸ h⟩

private abbrev productUnit : τ := product unit unit

private def rebuilt : ContinuationFamily (Φ := Φ) ([] : List τ) [productUnit] [productUnit] :=
  singleton (.let₂ (.var (i := 0) rfl) (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))

private def direct : ContinuationFamily (Φ := Φ) ([] : List τ) [productUnit] [productUnit] :=
  singleton (.br (ℓ := 0) rfl (.var (i := 0) rfl))

/-- The scope-indexed model admits unit at an input that has product or empty
type in the exact syntax. There are no primitive transitions at all. -/
private abbrev unitInput (Φ : Type u) : Model.{u,0,0} Φ 1 where
  α := Unit
  σ := Unit
  instr _ _ _ _ _ := False
  faults _ _ _ _ := False
  prim _ _ _ := False
  bound _ := .unit

theorem not_paper_family_descent :
    ¬ FamilyDescent.{u,v,0,0}
      (Paper.familySetoid (Φ := Φ) ([] : List τ) [product unit unit] [product unit unit]) := by
  intro ⟨lift, agrees⟩
  let S := Paper.familySetoid (Φ := Φ) ([] : List τ) [productUnit] [productUnit]
  have joined : Quotient.mk S rebuilt = Quotient.mk S direct := by
    apply Quotient.sound
    intro i A hi
    have same : A = (productUnit : τ) := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst A
    exact Paper.Eqv.productEta (.let₂Eta (i := 0) (ℓ := 0) rfl rfl)
  have equal := congrArg (fun q => lift q (0 : Fin 1) (unitInput Φ) ()) joined
  rw [agrees rebuilt (0 : Fin 1), agrees direct (0 : Fin 1)] at equal
  have returned : Outcome.ret (0 : Fin 1) .unit () ∈
      (familyDenotation.{u,v,0,0} (direct (Φ := Φ) (τ := τ)) 0 (unitInput Φ) ()).possible :=
    Semantics.Region.Eval.br Semantics.Tm.Eval.var
  rw [← equal] at returned
  change Semantics.Region.Eval (unitInput Φ).instr (envOfBound (unitInput Φ).bound)
    (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0)))) () 0 .unit () at returned
  cases returned with
  | let₂ arg _ => cases arg

private def emptyReturn : ContinuationFamily (Φ := Φ) ([] : List τ) [empty] [unit] :=
  singleton (.br (ℓ := 0) rfl .unit)

private def emptyAbort : ContinuationFamily (Φ := Φ) ([] : List τ) [empty] [unit] :=
  singleton (.let₁ (.abort (.var (i := 0) rfl) (A := (unit : τ))) (.br (ℓ := 0) rfl .unit))

theorem not_continuation_family_descent :
    ¬ FamilyDescent.{u,v,0,0} (continuationSetoid (Φ := Φ) ([] : List τ) [empty] [unit]) := by
  intro ⟨lift, agrees⟩
  let S := continuationSetoid (Φ := Φ) ([] : List τ) [empty] [unit]
  have joined : Quotient.mk S emptyAbort = Quotient.mk S emptyReturn := by
    apply Quotient.sound
    intro i A hi
    have same : A = (empty : τ) := List.mem_singleton.mp (List.mem_of_getElem? hi)
    subst A
    exact SubstitutionEquiv.initial (.var (i := 0) rfl)
      (.let₁ (.abort (.var (i := 0) rfl) (A := (unit : τ))) (.br (ℓ := 0) rfl .unit)) (.br (ℓ := 0) rfl .unit)
  have equal := congrArg (fun q => lift q (0 : Fin 1) (unitInput Φ) ()) joined
  rw [agrees emptyAbort (0 : Fin 1), agrees emptyReturn (0 : Fin 1)] at equal
  have returned : Outcome.ret (0 : Fin 1) .unit () ∈
      (familyDenotation.{u,v,0,0} (emptyReturn (Φ := Φ) (τ := τ)) 0 (unitInput Φ) ()).possible :=
    Semantics.Region.Eval.br Semantics.Tm.Eval.unit
  rw [← equal] at returned
  change Semantics.Region.Eval (unitInput Φ).instr (envOfBound (unitInput Φ).bound)
    (.let₁ (.abort (.var 0)) (.br 0 .unit)) () 0 .unit () at returned
  cases returned with
  | let₁ arg _ => cases arg

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay
