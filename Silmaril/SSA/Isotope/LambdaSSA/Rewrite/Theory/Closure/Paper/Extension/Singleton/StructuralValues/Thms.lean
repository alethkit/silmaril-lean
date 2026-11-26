module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues

/-! # The wide subcategory determined by the three structural equations -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

instance : (HomProperty Seed).IsMultiplicative where
  id_mem := Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues.id_mem Seed
  comp_mem := Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues.comp_mem Seed

/-- All central arrows preserving copy and discard in the quotient. -/
abbrev ValueCategory := WideSubcategory (HomProperty Seed)

/-- Include structural values into computations. -/
abbrev inclusion : ValueCategory Seed ⥤ TypeCategory Seed :=
  wideSubcategoryInclusion (HomProperty Seed)

/-- Copying and interchange let a common producer run before pairing. -/
theorem pair_comp {X Y A B : TypeCategory Seed} (f : X ⟶ Y) (g : Y ⟶ A) (h : Y ⟶ B)
    (hf : CentralCopies Seed f) :
    pairArrows Seed (f ≫ g) (f ≫ h) = f ≫ pairArrows Seed g h :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.StructuralValues.pair_comp Seed f g h hf

open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory
  (returnRegion_typed returnRegion_branchValue)

/-- A guarded branch of a constructor value satisfies all three structural equations. -/
theorem branch_mem {A B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a B) :
    HomProperty Seed (ofRegion Seed (.br (ℓ := 0) rfl ha)) :=
  ⟨map_centralCopies Seed ⟨Paper.TypeCategory.whiskerCentral_ofRegion_branchValue ha,
      Paper.TypeCategory.pairArrows_copy_branchValue ha⟩,
    ((projection Seed).map_comp _ _).symm.trans
      (congrArg (projection Seed).map (Paper.TypeCategory.discard_comp_branchValue ha))⟩

/-- Lowering a constructor-valued expression to a guarded return yields a structural value. -/
theorem return_mem {A B : τ} {a : Tm Φ} (ha : Tm.BranchValue [A] a B) :
    HomProperty Seed (ofRegion Seed (returnRegion_typed ha.hasType)) := by
  rw [(ofRegion_eq_iff Seed _ _).2 (.paper (.cfgEta (.native (.base (returnRegion_branchValue ha)))))]
  exact branch_mem Seed ha

variable {ε : Type w} [HasEff Φ ε] {pe : ε}

/-- Any of the previous certified pure returns is a structural value. -/
theorem of_discardPreservingReturn {X Y : TypeCategory Seed} {f : X ⟶ Y}
    (hf : DiscardPreservingReturn Seed pe f) : HomProperty Seed f :=
  ⟨hf.1.centralCopies, hf.2⟩

/-- Embed the previous discard-preserving value category over the same computation arrows. -/
@[expose] def fromPureReturns (pe : ε) : DiscardPreservingValueCategory Seed pe ⥤ ValueCategory Seed where
  obj X := ⟨X.obj⟩
  map f := ⟨f.hom, of_discardPreservingReturn Seed f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance (pe : ε) : (fromPureReturns Seed pe).Faithful :=
  ⟨fun h => WideSubcategory.hom_ext _ (congrArg (·.hom) h)⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
