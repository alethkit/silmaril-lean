module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.Category

/-! # The opt-in CFG η continuation category -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {Γ : VCtx τ}

instance interfaceCategory : Category.{v} (Interface Φ Γ) where
  Hom X Y := Hom (Φ := Φ) Γ X.labels Y.labels
  id X := Hom.identity Γ X.labels
  comp := Hom.compose
  id_comp := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.identity_compose
  comp_id := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.compose_identity
  assoc := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.compose_assoc

/-- The arrow represented by a typed family of continuations with value branches. -/
@[expose] def toHom {X Y : Interface Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) : X ⟶ Y :=
  Quotient.mk _ σ

theorem toHom_eq_iff {X Y : Interface Φ Γ}
    {σ υ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels} :
    toHom (X := X) (Y := Y) σ = toHom (X := X) (Y := Y) υ ↔
      Equivalent Γ X.labels Y.labels σ.val υ.val :=
  Quotient.eq

/-- Keep the exit interfaces and quotient native arrows by the additional CFG η equations. -/
@[expose] def fromNative : ContinuationContext Φ Γ ⥤ Interface Φ Γ where
  obj X := ⟨X.labels⟩
  map := Hom.ofNative
  map_id _ := rfl
  map_comp := by exact Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ofNative_compose

@[simp] theorem fromNative_map_toHom {X Y : ContinuationContext Φ Γ}
    (σ : ContinuationFamily (Φ := Φ) Γ X.labels Y.labels) :
    fromNative.map (σ.toHom (X := X) (Y := Y)) = toHom σ :=
  rfl

/-- Every arrow of the opt-in category has a lift to a native continuation class. -/
theorem fromNative_map_surjective {X Y : ContinuationContext Φ Γ} :
    Function.Surjective (fromNative.map : (X ⟶ Y) → (fromNative.obj X ⟶ fromNative.obj Y)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.ofNative_surjective

instance fromNative_full : (fromNative (Φ := Φ) (Γ := Γ)).Full where
  map_surjective := fromNative_map_surjective

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
