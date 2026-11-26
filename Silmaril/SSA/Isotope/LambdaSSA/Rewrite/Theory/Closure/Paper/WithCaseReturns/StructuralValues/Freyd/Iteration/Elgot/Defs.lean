module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

/-! # The remaining uniformity field for the case-return model -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues

open CategoryTheory CategoryTheory.Limits

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)

set_option hygiene false in
local notation "Comp" => Paper.WithCaseReturns.TypeCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "Val" => ValueCategory (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "inc" => inclusion (τ := τ) (Φ := Φ) pe

attribute [local instance] guardedIteration

/-- Uniformity for all structural value maps and commuting squares in the computation quotient. -/
def StructuralUniformity : Prop :=
  ∀ {A D : Val} {B : Comp}
    (f : (inc).obj A ⟶ B ⨿ (inc).obj A) (g : (inc).obj D ⟶ B ⨿ (inc).obj D) (h : A ⟶ D),
    f ≫ coprod.map (𝟙 B) ((inc).map h) = (inc).map h ≫ g →
      CategoryTheory.iterate f = (inc).map h ≫ CategoryTheory.iterate g

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues
