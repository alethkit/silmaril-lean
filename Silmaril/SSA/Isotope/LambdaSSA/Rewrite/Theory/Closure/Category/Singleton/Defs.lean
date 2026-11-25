module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Coproducts.Defs

/-! # Singleton interfaces and the syntactic sum in native λSSA -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.ContinuationContext

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The interface with one label accepting a value of type `A`. -/
@[expose] def single (A : τ) : ContinuationContext Φ Γ := ⟨[A]⟩

/-- Treat a typed region as the only arm of a continuation family. -/
@[expose] def singletonToHom {A : τ} {Y : ContinuationContext Φ Γ} {r : Region Φ}
    (hr : ValueBranches (A :: Γ) r Y.labels) : single A ⟶ Y :=
  ContinuationFamily.toHom ⟨fun _ => r, fun _ D hi => by
    have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    simpa only [eq] using hr⟩

/-- Tag the payload from the left or right label with the corresponding injection. -/
@[expose] def sumTagRegion (i : Nat) : Region Φ :=
  if i = 0 then .br 0 (.inl (.var 0)) else .br 0 (.inr (.var 0))

/-- Case analysis routes the payload to the appropriate label of the pair. -/
@[expose] def sumCase (A B : τ) :
    (single (Silmaril.coprod A B) : ContinuationContext Φ Γ) ⟶ (single A).append (single B) :=
  singletonToHom (.case (A := A) (B := B) (.var (i := 0) rfl)
    (.br (ℓ := 0) rfl (.var (i := 0) rfl)) (.br (ℓ := 1) rfl (.var (i := 0) rfl)))

end Silmaril.Isotope.LambdaSSA.Region.ContinuationContext
