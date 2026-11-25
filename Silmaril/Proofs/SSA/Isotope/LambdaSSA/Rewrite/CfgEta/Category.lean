module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Defs

/-! # Category laws for one-block CFG η continuation classes -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L K P Q : LCtx τ}

theorem ofNative_compose (f : ContinuationHom (Φ := Φ) Γ L K)
    (g : ContinuationHom (Φ := Φ) Γ K P) :
    Hom.ofNative (f.compose g) = (Hom.ofNative f).compose (Hom.ofNative g) :=
  Quotient.inductionOn₂ f g (fun _ _ => rfl)

theorem ofNative_surjective :
    Function.Surjective (Hom.ofNative : ContinuationHom (Φ := Φ) Γ L K → Hom Γ L K) :=
  fun f => Quotient.inductionOn f (fun σ => ⟨Quotient.mk _ σ, rfl⟩)

theorem identity_compose (f : Hom (Φ := Φ) Γ L K) : (Hom.identity Γ L).compose f = f := by
  obtain ⟨f, rfl⟩ := ofNative_surjective f
  rw [← show Hom.ofNative (ContinuationHom.identity (Φ := Φ) Γ L) = Hom.identity Γ L from rfl,
    ← ofNative_compose, ContinuationHom.identity_compose]

theorem compose_identity (f : Hom (Φ := Φ) Γ L K) : f.compose (Hom.identity Γ K) = f := by
  obtain ⟨f, rfl⟩ := ofNative_surjective f
  rw [← show Hom.ofNative (ContinuationHom.identity (Φ := Φ) Γ K) = Hom.identity Γ K from rfl,
    ← ofNative_compose, ContinuationHom.compose_identity]

theorem compose_assoc (f : Hom (Φ := Φ) Γ L K) (g : Hom (Φ := Φ) Γ K P)
    (h : Hom (Φ := Φ) Γ P Q) : (f.compose g).compose h = f.compose (g.compose h) := by
  obtain ⟨f, rfl⟩ := ofNative_surjective f
  obtain ⟨g, rfl⟩ := ofNative_surjective g
  obtain ⟨h, rfl⟩ := ofNative_surjective h
  simp only [← ofNative_compose, ContinuationHom.compose_assoc]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta
