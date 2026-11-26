module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Coproducts.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueCoproducts

/-! # The structural value inclusion preserves finite coproducts -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Obj" => ofType (Φ := Φ) Seed
local notation "Val" => ValueCategory Seed
local notation "H" => HomProperty Seed

open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The computation copair preserves the three equations. -/
theorem copair_mem {A B : τ} {D : TypeCategory Seed} {f : Obj A ⟶ D} {g : Obj B ⟶ D}
    (hf : H f) (hg : H g) : H (exactCopair Seed f g) :=
  StructuralValueCoproducts.copair_mem Seed hf hg

/-- The guarded binary sum is a coproduct in the structural value category. -/
noncomputable def sumIsColimit (A B : τ) : IsColimit (sum Seed A B) :=
  StructuralValueCoproducts.sumIsColimit Seed A B

/-- The guarded empty type is initial in the structural value category. -/
noncomputable def emptyIsInitial : IsInitial (⟨Obj (Silmaril.empty : τ)⟩ : Val) :=
  StructuralValueCoproducts.emptyIsInitial Seed

theorem hasFiniteCoproducts : HasFiniteCoproducts Val :=
  StructuralValueCoproducts.valueHasFiniteCoproducts Seed

theorem preservesFiniteCoproducts : PreservesFiniteCoproducts (inclusion Seed) :=
  StructuralValueCoproducts.valuePreservesFiniteCoproducts Seed

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
