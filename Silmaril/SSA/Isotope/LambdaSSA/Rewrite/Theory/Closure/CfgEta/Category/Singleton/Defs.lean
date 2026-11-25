module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Defs

/-! # Types as singleton interfaces in the CFG η quotient -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

/-- Single-label objects in the continuation category for one-block CFG η. -/
abbrev TypeCategory (Φ : Type v) [HasTy Φ τ] (Γ : VCtx τ) :=
  InducedCategory (Interface Φ Γ) (fun A : τ => fromNative.obj (ContinuationContext.single A))

namespace TypeCategory

@[expose] def ofType (A : τ) : TypeCategory Φ Γ := A

abbrev toInterface (Φ : Type v) [HasTy Φ τ] (Γ : VCtx τ) : TypeCategory Φ Γ ⥤ Interface Φ Γ :=
  inducedFunctor (fun A : τ => fromNative.obj (ContinuationContext.single A))

/-- A region with one input and one exit gives an arrow in the enlarged type category. -/
@[expose] def ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches (A :: Γ) r [B]) :
    ofType (Φ := Φ) A ⟶ ofType (Γ := Γ) B :=
  InducedCategory.homMk (fromNative.map (ContinuationContext.singletonToHom hr))

/-- The two singleton injections tag their payload for the sum-typed exit. -/
@[expose] def sumCofan (A B : τ) : BinaryCofan (ofType (Φ := Φ) (Γ := Γ) A) (ofType B) :=
  let X : ContinuationContext Φ Γ := ContinuationContext.single A
  let Y : ContinuationContext Φ Γ := ContinuationContext.single B
  BinaryCofan.mk
    (InducedCategory.homMk (Y := ofType (Silmaril.coprod A B))
      (fromNative.map (X.appendInl Y ≫ ContinuationContext.sumTag A B)))
    (InducedCategory.homMk (fromNative.map (X.appendInr Y ≫ ContinuationContext.sumTag A B)))

end TypeCategory

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
