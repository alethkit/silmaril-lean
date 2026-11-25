module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Thms

/-! # Composition and identities for the paper quotient -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category

open CategoryTheory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper (Hom)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P Q : LCtx τ}

theorem ofCfgEta_compose (f : CfgEta.Hom (Φ := Φ) Γ L K) (g : CfgEta.Hom (Φ := Φ) Γ K P) :
    Hom.ofCfgEta (f.compose g) = (Hom.ofCfgEta f).compose (Hom.ofCfgEta g) :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem ofCfgEta_surjective :
    Function.Surjective (Hom.ofCfgEta : CfgEta.Hom (Φ := Φ) Γ L K → Hom Γ L K) :=
  fun f => Quotient.inductionOn f (fun σ => ⟨Quotient.mk _ σ, rfl⟩)

private theorem representatives_equal {σ υ : ContinuationFamily (Φ := Φ) Γ L K}
    (h : σ.val = υ.val) : (Quotient.mk (Paper.familySetoid Γ L K) σ : Hom Γ L K) = Quotient.mk _ υ :=
  congrArg (Quotient.mk (Paper.familySetoid Γ L K)) (Subtype.ext h)

theorem identity_compose (f : Hom (Φ := Φ) Γ L K) : (Hom.identity Γ L).compose f = f := by
  induction f using Quotient.inductionOn with
  | h σ => exact representatives_equal (compLSubst_id_left σ.val)

theorem compose_identity (f : Hom (Φ := Φ) Γ L K) : f.compose (Hom.identity Γ K) = f := by
  induction f using Quotient.inductionOn with
  | h σ => exact representatives_equal (compLSubst_id_right σ.val)

theorem compose_assoc (f : Hom (Φ := Φ) Γ L K) (g : Hom (Φ := Φ) Γ K P)
    (h : Hom (Φ := Φ) Γ P Q) : (f.compose g).compose h = f.compose (g.compose h) := by
  induction f, g, h using Quotient.inductionOn₃ with
  | h σ υ ω => exact representatives_equal (compLSubst_assoc σ.val υ.val ω.val)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Category
