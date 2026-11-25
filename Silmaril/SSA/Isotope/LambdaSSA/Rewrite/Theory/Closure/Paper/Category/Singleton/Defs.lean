module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Thms

/-! # Empty-capture singleton interfaces in the paper relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The full category on single-label interfaces with empty capture. -/
abbrev TypeCategory (Φ : Type v) [HasTy Φ τ] :=
  InducedCategory (Interface Φ ([] : VCtx τ)) (fun A : τ => ⟨[A]⟩)

namespace TypeCategory

abbrev ofType (A : τ) : TypeCategory (τ := τ) Φ := A

/-- A typed region with constructor-valued branches represents a singleton arrow. -/
@[expose] def ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    ofType (Φ := Φ) A ⟶ ofType B :=
  InducedCategory.homMk (toHom ⟨fun _ => r, fun _ D hi => by
    change ValueBranches (D :: []) r [B]
    have eq : D = A := List.mem_singleton.mp (List.mem_of_getElem? hi)
    simpa only [eq] using hr⟩)

end TypeCategory
end Silmaril.Isotope.LambdaSSA.Region.Paper
