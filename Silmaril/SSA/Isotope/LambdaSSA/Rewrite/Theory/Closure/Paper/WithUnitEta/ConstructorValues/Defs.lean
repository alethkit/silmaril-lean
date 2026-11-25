module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms

/-! # Constructor returns in the guarded unit quotient -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- Include the original constructor-return category into the unit extension. -/
abbrev constructorReturns :
    WideSubcategory (Paper.TypeCategory.ConstructorReturn (τ := τ) (Φ := Φ)) ⥤
      TypeCategory (τ := τ) (Φ := Φ) :=
  wideSubcategoryInclusion _ ⋙ projection

/-- Keep exactly the constructor-return arrows, with equality inherited from the unit extension. -/
abbrev ConstructorValueCategory :=
  CategoryTheory.Quotient (constructorReturns (τ := τ) (Φ := Φ)).homRel

/-- The inclusion of constructor arrows with the inherited equality. -/
def constructorValues : ConstructorValueCategory (τ := τ) (Φ := Φ) ⥤ TypeCategory (τ := τ) (Φ := Φ) :=
  CategoryTheory.Quotient.lift _ constructorReturns (fun _ _ _ _ h => h)

/-- The object determined by the syntax unit type. -/
def constructorUnit : ConstructorValueCategory (τ := τ) (Φ := Φ) :=
  (CategoryTheory.Quotient.functor _).obj ⟨Paper.TypeCategory.ofType Silmaril.unit⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithUnitEta
