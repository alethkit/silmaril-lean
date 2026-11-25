module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category

/-! # The category of typed continuation classes in the paper relation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

instance interfaceCategory : Category.{v} (Interface Φ Γ) where
  Hom X Y := Hom (Φ := Φ) Γ X.labels Y.labels
  id X := Hom.identity Γ X.labels
  comp := Hom.compose
  id_comp := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category.identity_compose
  comp_id := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category.compose_identity
  assoc := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category.compose_assoc

/-- A typed family with constructor-valued branch arguments represents an arrow. -/
@[expose] def toHom {X Y : Interface Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) : X ⟶ Y :=
  Quotient.mk _ σ

theorem toHom_eq_iff {X Y : Interface Φ Γ}
    {σ υ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels} :
    toHom (X := X) (Y := Y) σ = toHom (X := X) (Y := Y) υ ↔
      ∀ ⦃i A⦄, At X.labels i A → Eqv (A :: Γ) (σ.val i) (υ.val i) Y.labels :=
  Quotient.eq

/-- Pass from the CFG η quotient to the paper quotient on the same interfaces. -/
@[expose] def fromCfgEta : CfgEta.Interface Φ Γ ⥤ Interface Φ Γ where
  obj X := ⟨X.labels⟩
  map := Hom.ofCfgEta
  map_id _ := rfl
  map_comp := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category.ofCfgEta_compose

@[simp] theorem fromCfgEta_map_toHom {X Y : CfgEta.Interface Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) :
    fromCfgEta.map (CfgEta.toHom (X := X) (Y := Y) σ) = toHom σ := rfl

instance fromCfgEta_full : (fromCfgEta (Φ := Φ) (Γ := Γ)).Full where
  map_surjective := Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category.ofCfgEta_surjective

end Silmaril.Isotope.LambdaSSA.Region.Paper
