module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchNormalization

/-! # Round trips for joined branch normalization -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "E" => Extension.Eqv (Step (τ := τ) (Φ := Φ))

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Guarded classes are a retract of the classes of all exactly typed regions. -/
@[simp] theorem normalize_toRaw (q : GuardedRegionClass (Φ := Φ) Γ L) :
    normalize (toRaw q) = q :=
  Quot.inductionOn q fun r =>
    Quot.sound (.paper (.cfgEta (.native r.property.substitutionEquiv_bindBranchArguments.symm)))

theorem rawClass_eq_iff (hr : HasType Γ r L) (hs : HasType Γ s L) :
    rawClass hr = rawClass hs ↔ E Γ r s L :=
  Quotient.eq

/-- The reverse round trip at a raw representative is exactly a joined rewrite equation. -/
theorem toRaw_normalize_mk_iff (hr : HasType Γ r L) :
    toRaw (normalize (rawClass hr)) = rawClass hr ↔ E Γ r.bindBranchArguments r L :=
  rawClass_eq_iff hr.bindBranchArguments.hasType hr

/-- To obtain the reverse round trip for all raw classes, it suffices to prove the
typed single-branch bind equation. Region contexts then transport it under arbitrary CFGs. -/
theorem bindBranchArguments_eqv_of_br
    (bindBr : ∀ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {ℓ : Nat} {A : τ},
      At L ℓ A → Tm.HasType Γ a A → E Γ (.let₁ a (.br ℓ (.var 0))) (.br ℓ a) L)
    (hr : HasType Γ r L) : E Γ r.bindBranchArguments r L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchNormalization.bindBranchArguments_eqv_of_br bindBr hr

/-- The raw round trip at every interface is equivalent to the typed branch
equation, with no constructor-value requirement on its argument. -/
theorem raw_roundtrip_iff_br :
    (∀ (Γ : VCtx τ) (L : LCtx τ) (q : RawRegionClass (Φ := Φ) Γ L), toRaw (normalize q) = q) ↔
    (∀ {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {ℓ : Nat} {A : τ},
      At L ℓ A → Tm.HasType Γ a A → E Γ (.let₁ a (.br ℓ (.var 0))) (.br ℓ a) L) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedBranchNormalization.raw_roundtrip_iff_br

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization
