module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Tensor.Thms

/-! # Guarded reassociation of singleton product types -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Obj" => ofType (τ := τ) (Φ := Φ)
local infixr:70 " ×ₜ " => product

def associateRegion {Φ : Type v} : Region Φ :=
  .let₂ (.var 0) (.let₂ (.var 1) (.br 0 (.pair (.var 1) (.pair (.var 0) (.var 2)))))

def unassociateRegion {Φ : Type v} : Region Φ :=
  .let₂ (.var 0) (.let₂ (.var 0) (.br 0 (.pair (.pair (.var 3) (.var 1)) (.var 0))))

theorem associate_typed (A B C : τ) :
    ValueBranches [(A ×ₜ B) ×ₜ C] (associateRegion : Region Φ) [A ×ₜ B ×ₜ C] :=
  .let₂ (.var rfl) (.let₂ (.var rfl) (.br rfl (.pair (.var rfl) (.pair (.var rfl) (.var rfl)))))

theorem unassociate_typed (A B C : τ) :
    ValueBranches [A ×ₜ B ×ₜ C] (unassociateRegion : Region Φ) [(A ×ₜ B) ×ₜ C] :=
  .let₂ (.var rfl) (.let₂ (.var rfl) (.br rfl (.pair (.pair (.var rfl) (.var rfl)) (.var rfl))))

abbrev associate (A B C : τ) : Obj ((A ×ₜ B) ×ₜ C) ⟶ Obj (A ×ₜ B ×ₜ C) :=
  ofRegion (associate_typed A B C)

abbrev unassociate (A B C : τ) : Obj (A ×ₜ B ×ₜ C) ⟶ Obj ((A ×ₜ B) ×ₜ C) :=
  ofRegion (unassociate_typed A B C)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
