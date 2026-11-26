module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Product.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Projections.Thms
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Guarded product choices for structural values -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Val" => ValueCategory Seed
local notation "H" => HomProperty Seed
local notation "U" => (Silmaril.unit : τ)
local infixr:70 " ×ₜ " => Silmaril.product

theorem fst_mem (A B : τ) : H (productFst Seed A B) :=
  ⟨map_centralCopies Seed (Paper.TypeCategory.centralCopies_productFst A B), fst_discard Seed A B⟩

theorem snd_mem (A B : τ) : H (productSnd Seed A B) :=
  ⟨map_centralCopies Seed (Paper.TypeCategory.centralCopies_productSnd A B), snd_discard Seed A B⟩

def productFan (A B : τ) :
    BinaryFan (⟨Obj A⟩ : Val) ⟨Obj B⟩ :=
  BinaryFan.mk (P := (⟨Obj (A ×ₜ B)⟩ : Val))
    ⟨productFst Seed A B, fst_mem Seed A B⟩ ⟨productSnd Seed A B, snd_mem Seed A B⟩

/-- Build the Cartesian tensor on the exact syntax objects and guarded projection fan. -/
noncomputable abbrev cartesianOfLimits
    (unitLimit : IsTerminal (⟨Obj U⟩ : Val))
    (binaryLimit : ∀ (A B : τ), IsLimit (productFan Seed A B)) : CartesianMonoidalCategory Val :=
  CartesianMonoidalCategory.ofChosenFiniteProducts ⟨_, unitLimit⟩
    (fun X Y => ⟨productFan Seed X.obj.as Y.obj.as, binaryLimit X.obj.as Y.obj.as⟩)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
