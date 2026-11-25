module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Copy.Thms

/-! # Sequential tensor on arrows and the guarded middle-four shuffle -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

abbrev tensorSequence {A B C D : τ} (f : Obj A ⟶ Obj C) (g : Obj B ⟶ Obj D) :
    Obj (A ×ₜ B) ⟶ Obj (C ×ₜ D) :=
  whiskerRight f (Obj B) ≫ whiskerLeft (Obj C) g

def middleFourRegion {Φ : Type v} : Region Φ :=
  .let₂ (.var 0) (.let₂ (.var 1) (.let₂ (.var 2)
    (.br 0 (.pair (.pair (.var 3) (.var 1)) (.pair (.var 2) (.var 0))))))

theorem middleFour_typed (A C B D : τ) :
    ValueBranches [(A ×ₜ C) ×ₜ (B ×ₜ D)] (middleFourRegion : Region Φ) [(A ×ₜ B) ×ₜ (C ×ₜ D)] :=
  .let₂ (.var rfl) (.let₂ (.var rfl) (.let₂ (.var rfl)
    (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.pair (.var rfl) (.var rfl))))))

def middleFour (A C B D : τ) :
    Obj ((A ×ₜ C) ×ₜ (B ×ₜ D)) ⟶ Obj ((A ×ₜ B) ×ₜ (C ×ₜ D)) :=
  ofRegion (middleFour_typed A C B D)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
