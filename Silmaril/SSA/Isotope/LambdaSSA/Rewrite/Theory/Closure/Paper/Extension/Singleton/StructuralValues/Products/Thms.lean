module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithUnitEta.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValueProducts

/-! # Cartesian structure of structural values -/

public section

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

open scoped MonoidalCategory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- The pair of two structural arrows again satisfies all three equations. -/
theorem pair_mem {X A B : τ} {f : Obj X ⟶ Obj A} {g : Obj X ⟶ Obj B}
    (hf : H f) (hg : H g) : H (pairArrows Seed f g) :=
  StructuralValueProducts.pair_mem Seed hf hg

/-- A structural arrow into a product is determined by its two guarded projections. -/
theorem reconstruct {X A B : τ} {f : Obj X ⟶ Obj (A ×ₜ B)} (hf : H f) :
    pairArrows Seed (f ≫ productFst Seed A B) (f ≫ productSnd Seed A B) = f :=
  StructuralValueProducts.reconstruct Seed hf

/-- The exact guarded product projections are limiting. -/
noncomputable def productIsLimit (A B : τ) : IsLimit (productFan Seed A B) :=
  StructuralValueProducts.productIsLimit Seed A B

variable (includeUnit : ∀ {Γ : VCtx τ} {r s : Region Φ} {K : LCtx τ},
  Paper.WithUnitEta.Step Γ r s K → Seed Γ r s K)

/-- The unit-η equation makes the guarded unit terminal. -/
noncomputable def unitIsTerminal : IsTerminal (⟨Obj U⟩ : Val) :=
  StructuralValueProducts.unitIsTerminal Seed includeUnit

/-- The Cartesian monoidal structure using the guarded products and terminal object. -/
noncomputable abbrev cartesian : CartesianMonoidalCategory Val :=
  cartesianOfLimits Seed (unitIsTerminal Seed includeUnit) (productIsLimit Seed)

/-- The inclusion preserves the exact left whiskering. -/
theorem map_whiskerLeft (X : τ) {A B : τ} (f : (⟨Obj A⟩ : Val) ⟶ ⟨Obj B⟩) :
    letI := cartesian Seed includeUnit
    (inclusion Seed).map ((⟨Obj X⟩ : Val) ◁ f) = whiskerLeft Seed (Obj X) f.hom :=
  StructuralValueProducts.map_whiskerLeft Seed (unitIsTerminal Seed includeUnit) (productIsLimit Seed) X f

/-- The inclusion preserves the exact right whiskering. -/
theorem map_whiskerRight (X : τ) {A B : τ} (f : (⟨Obj A⟩ : Val) ⟶ ⟨Obj B⟩) :
    letI := cartesian Seed includeUnit
    (inclusion Seed).map (f ▷ (⟨Obj X⟩ : Val)) = whiskerRight Seed f.hom (Obj X) :=
  StructuralValueProducts.map_whiskerRight Seed (unitIsTerminal Seed includeUnit) (productIsLimit Seed) X f

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
