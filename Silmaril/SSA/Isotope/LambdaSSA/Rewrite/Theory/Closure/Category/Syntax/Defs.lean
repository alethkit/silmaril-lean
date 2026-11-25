module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Singleton.Defs
public import Mathlib.CategoryTheory.InducedCategory

/-! # The type objects of the native LambdaSSA syntactic category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- The category of types and native continuation arrows between single-label
interfaces, over a fixed context of captured variables. -/
abbrev SyntacticCategory (Φ : Type v) [HasTy Φ τ] (Γ : VCtx τ) :=
  InducedCategory (ContinuationContext Φ Γ) (fun A : τ => ContinuationContext.single A)

namespace SyntacticCategory

/-- Regard a signature type as an object of the syntactic category. -/
@[expose] def ofType (A : τ) : SyntacticCategory Φ Γ := A

/-- Include type objects into the category of arbitrary exit interfaces. -/
abbrev toContinuation (Φ : Type v) [HasTy Φ τ] (Γ : VCtx τ) :
    SyntacticCategory Φ Γ ⥤ ContinuationContext Φ Γ :=
  inducedFunctor (fun A : τ => ContinuationContext.single A)

/-- A region with one input and one exit represents a syntactic arrow. -/
@[expose] def ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches (A :: Γ) r [B]) :
    ofType (Φ := Φ) A ⟶ ofType (Γ := Γ) B :=
  InducedCategory.homMk (ContinuationContext.singletonToHom hr)

/-- Take the syntactic arrow of an exactly typed region after binding each
branch argument once. -/
@[expose] def ofTypedRegion {A B : τ} {r : Region Φ} (hr : HasType (A :: Γ) r [B]) :
    ofType (Φ := Φ) A ⟶ ofType (Γ := Γ) B :=
  ofRegion hr.bindBranchArguments

end SyntacticCategory
end Silmaril.Isotope.LambdaSSA.Region
