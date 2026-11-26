module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Thms

/-! # Guarded coproduct cocones for structural values -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Val" => ValueCategory Seed
local notation "H" => HomProperty Seed


set_option backward.isDefEq.respectTransparency false in
theorem sum_inl_mem (A B : τ) : H (sumCofan Seed A B).inl := by
  change H ((projection Seed).map (Paper.TypeCategory.sumCofan A B).inl)
  rw [Paper.TypeCategory.sumCofan_inl]
  exact branch_mem Seed (.inl (.var rfl))

set_option backward.isDefEq.respectTransparency false in
theorem sum_inr_mem (A B : τ) : H (sumCofan Seed A B).inr := by
  change H ((projection Seed).map (Paper.TypeCategory.sumCofan A B).inr)
  rw [Paper.TypeCategory.sumCofan_inr]
  exact branch_mem Seed (.inr (.var rfl))

/-- The exact syntax sum, with constructor injections certified structurally. -/
def sum (A B : τ) : BinaryCofan (⟨Obj A⟩ : Val) ⟨Obj B⟩ :=
  BinaryCofan.mk (P := (⟨Obj (Silmaril.coprod A B)⟩ : Val))
    ⟨(sumCofan Seed A B).inl, sum_inl_mem Seed A B⟩
    ⟨(sumCofan Seed A B).inr, sum_inr_mem Seed A B⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
