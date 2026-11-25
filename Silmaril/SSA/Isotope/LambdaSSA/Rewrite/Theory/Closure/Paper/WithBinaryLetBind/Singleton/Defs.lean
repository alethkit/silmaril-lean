module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBinaryLetBind.Defs

/-! # The binary-let extension on singleton arrows -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- The Paper singleton category quotiented by the binary-let extension. -/
abbrev TypeCategory (Φ : Type v) [HasTy Φ τ] :=
  Extension.Singleton.TypeCategory (BinaryLetBind.Step (τ := τ) (Φ := Φ))

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) Φ :=
  Extension.Singleton.projection BinaryLetBind.Step

abbrev ofType (A : τ) : TypeCategory (τ := τ) Φ :=
  (projection (Φ := Φ)).obj (Paper.TypeCategory.ofType (Φ := Φ) A)

abbrev ofRegion {A B : τ} {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    ofType (Φ := Φ) A ⟶ ofType (Φ := Φ) B :=
  (projection (Φ := Φ)).map (Paper.TypeCategory.ofRegion hr)

abbrev whiskerLeftFunctor (X : TypeCategory (τ := τ) Φ) :
    TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) Φ :=
  Extension.Singleton.whiskerLeftFunctor BinaryLetBind.Step X

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBinaryLetBind.Singleton
