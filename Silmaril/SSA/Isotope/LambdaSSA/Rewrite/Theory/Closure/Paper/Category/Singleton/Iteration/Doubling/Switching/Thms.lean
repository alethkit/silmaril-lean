module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling

/-! # Double iteration of a native two-state switch -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X Y B : τ}

local notation "Obj" => ofType (Φ := Φ)
local notation "S" => Obj (Silmaril.coprod X Y)

/-- When both native rows repeat into the opposite summand, the single
and doubled iterates agree. The row arrows can execute arbitrary effects. -/
theorem iterate_double_of_switching_rows (g : S ⟶ Obj B ⨿ S)
    (left : Obj X ⟶ Obj Y) (right : Obj Y ⟶ Obj X)
    (hl : (sumCofan X Y).inl ≫ g = left ≫ (sumCofan X Y).inr ≫ coprod.inr)
    (hr : (sumCofan X Y).inr ≫ g = right ≫ (sumCofan X Y).inl ≫ coprod.inr) :
    iterate (g ≫ coprod.desc coprod.inl g) = iterate g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SwitchingDoubling.iterate_double_of_switching_rows g left right hl hr

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
