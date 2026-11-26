module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnUniformity

/-! # Uniformity for let-bound returns and factorized squares -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits
open CfgEta.TypeCategory (returnRegion)
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A D E B : τ} {a b : Tm Φ}

local notation "Comp" => TypeCategory (τ := τ) Φ

/-- The guarded return of a constructor value contracts to the literal branch. -/
theorem returnTerm_branchValue (ha : Tm.BranchValue [A] a D) :
    returnTerm ha.hasType = ofRegion (.br (ℓ := 0) rfl ha) :=
  ReturnUniformity.returnTerm_branchValue ha

/-- The body of the let can refer to both the bound constructor value and the original input. -/
theorem constructorReturn_let (ha : Tm.BranchValue [A] a D)
    (hb : Tm.BranchValue [D, A] b E) :
    ConstructorReturn (returnTerm (.let₁ ha.hasType hb.hasType)) :=
  ReturnUniformity.constructorReturn_let ha hb

instance constructorReturn_multiplicative : (ConstructorReturn (τ := τ) (Φ := Φ)).IsMultiplicative where
  id_mem := ReturnUniformity.constructorReturn_id
  comp_mem _ _ := ReturnUniformity.constructorReturn_comp

/-- Uniformity applies to a state change with any constructor representative in the quotient. -/
theorem iterate_uniformity_ofConstructorReturn {X Y Z : Comp} {h : X ⟶ Y}
    (hh : ConstructorReturn h) (f : X ⟶ Z ⨿ X) (g : Y ⟶ Z ⨿ Y)
    (comm : f ≫ coprod.map (𝟙 Z) h = h ≫ g) :
    iterate f = h ≫ iterate g :=
  ReturnUniformity.iterate_uniformity_ofConstructorReturn hh f g comm

/-- A syntactic reduction of a typed return to a constructor suffices for a simulation square. -/
theorem iterate_uniformity_ofReturnTerm {X Y Z : τ} {a c : Tm Φ}
    (ha : Tm.HasType [X] a Y) (hc : Tm.BranchValue [X] c Y)
    (e : Paper.Eqv [X] (returnRegion a) (.br 0 c) [Y])
    (f : ofType (Φ := Φ) X ⟶ ofType Z ⨿ ofType X)
    (g : ofType (Φ := Φ) Y ⟶ ofType Z ⨿ ofType Y)
    (comm : f ≫ coprod.map (𝟙 (ofType Z)) (returnTerm ha) = returnTerm ha ≫ g) :
    iterate f = returnTerm ha ≫ iterate g :=
  ReturnUniformity.iterate_uniformity_ofReturnTerm ha hc e f g comm

/-- Two eliminations of the same alternating loop yield dinaturality for arbitrary arrows. -/
theorem iterate_dinaturality {X Y Z : Comp}
    (g : X ⟶ Y ⨿ Z) (h : Z ⟶ Y ⨿ X) :
    iterate (g ≫ coprod.desc coprod.inl h) =
      g ≫ coprod.desc (𝟙 Y) (iterate (h ≫ coprod.desc coprod.inl g)) :=
  ReturnUniformity.iterate_dinaturality g h

/-- Rotate an alternating loop when its first transition returns only a new state. -/
theorem iterate_roll {X Y Z : Comp} (h : X ⟶ Z) (step : Z ⟶ Y ⨿ X) :
    iterate (h ≫ step) = h ≫ iterate (step ≫ coprod.map (𝟙 Y) h) :=
  ReturnUniformity.iterate_roll h step

/-- An intermediate step that factors both sides suffices for a typed return to commute with feedback. -/
theorem iterate_uniformity_ofFactorization (ha : Tm.HasType [A] a D)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (step : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType A)
    (hf : f = returnTerm ha ≫ step)
    (hg : g = step ≫ coprod.map (𝟙 (ofType B)) (returnTerm ha)) :
    iterate f = returnTerm ha ≫ iterate g :=
  ReturnUniformity.iterate_uniformity_ofFactorization ha f g step hf hg

/-- An inverse of the typed return makes the ordinary simulation square sufficient. -/
theorem iterate_uniformity_ofReturnIso (ha : Tm.HasType [A] a D)
    (e : ofType (Φ := Φ) A ≅ ofType D) (he : e.hom = returnTerm ha)
    (f : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (g : ofType (Φ := Φ) D ⟶ ofType B ⨿ ofType D)
    (comm : f ≫ coprod.map (𝟙 (ofType B)) (returnTerm ha) = returnTerm ha ≫ g) :
    iterate f = returnTerm ha ≫ iterate g :=
  ReturnUniformity.iterate_uniformity_ofReturnIso ha e he f g comm

/-- A repeat-only step that preserves the constructor discard has the
same iteration when taken twice. The state update may change its payload. -/
theorem iterate_double_of_preservesDiscard {X Y : Comp} (h : X ⟶ X)
    (keepDiscard : PreservesDiscard h) :
    let g := h ≫ (coprod.inr : X ⟶ Y ⨿ X)
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  ReturnUniformity.iterate_double_of_preservesDiscard h keepDiscard

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
