module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.ConstructorValues.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # Terminality for projected constructor returns -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEtaConstructorValues

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false in
theorem constructorValues_faithful : (constructorValues (τ := τ) (Φ := Φ)).Faithful where
  map_injective {X Y} f g h := by
    let cut := CategoryTheory.Quotient.functor (constructorReturns (τ := τ) (Φ := Φ)).homRel
    obtain ⟨f', rfl⟩ := cut.map_surjective (X := X.as) (Y := Y.as) f
    obtain ⟨g', rfl⟩ := cut.map_surjective (X := X.as) (Y := Y.as) g
    exact CategoryTheory.Quotient.sound _ h

set_option backward.isDefEq.respectTransparency false in
noncomputable def constructorUnitIsTerminal :
    IsTerminal (constructorUnit (τ := τ) (Φ := Φ)) := by
  let P := Paper.TypeCategory.ConstructorReturn (τ := τ) (Φ := Φ)
  let F := constructorReturns (τ := τ) (Φ := Φ)
  let cut := CategoryTheory.Quotient.functor F.homRel
  let unitObject : WideSubcategory P := ⟨Paper.TypeCategory.ofType Silmaril.unit⟩
  let drop (X : WideSubcategory P) : X ⟶ unitObject :=
    ⟨Paper.TypeCategory.discardArrow (Φ := Φ) (show τ from X.obj), .unit, .unit, rfl⟩
  refine IsTerminal.ofUniqueHom (fun X => cut.map (drop X.as)) ?_
  intro X f
  obtain ⟨g, rfl⟩ := cut.map_surjective (X := X.as) (Y := unitObject) f
  apply CategoryTheory.Quotient.sound
  obtain ⟨a, ha, eq⟩ := g.2
  change projection.map g.1 = projection.map (Paper.TypeCategory.discardArrow (Φ := Φ) (show τ from X.as.obj))
  rw [eq]
  exact (Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ofRegion_eq_iff Step _ _).2
    (branch_unit_eta ha (rfl : At [(Silmaril.unit : τ)] 0 Silmaril.unit)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithUnitEtaConstructorValues
