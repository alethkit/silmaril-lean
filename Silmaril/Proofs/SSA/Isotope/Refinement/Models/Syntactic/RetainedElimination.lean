module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyNaturality

/-! # Eliminating an effect while retaining a copied input -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- A returned unit can be replaced by the canonical unit while retaining
the original input. The computation producing it is still executed. -/
theorem unit_pair_bind (hR : R.RenamingClosed) {A : τ} {a : Term Φ 1}
    (hA : Quantity.relevant ≤ quantity A) (ha : HasType F (input A) (⊤ : ε) a Silmaril.unit) :
    Equates (ε := ε) F R (input A) (.pair a (.bv 0))
      (.let₁ a (.pair .unit (.bv 1))) (product Silmaril.unit A) := by
  have h₀ := pair_left_bind_any (R := R) (input_diagonal A hA) ha (identityDeriv A (⊤ : ε))
  have hu := (unitVariable_equates (F := F) (R := R) (Φ := Φ) (ε := ε)).rename _
    ((QCtx.Weakening.insertZero QCtx.nil A).up Silmaril.unit) hR
  have hv := (identityDeriv (F := F) (Φ := Φ) A (⊤ : ε)).rename Fin.succ
    (QCtx.Weakening.insertZero (input A) Silmaril.unit)
  have hb := Equates.pair ((inputSplit A).snoc (.left (.used ⊤))) hu (Equates.refl ⟨hv⟩)
  exact h₀.trans (Equates.let₁ (input_diagonal A hA) (Equates.refl ⟨ha⟩) hb)

/-- The written elimination rule can remove a unit computation sharing a
relevant input with the continuation that retains that input. -/
theorem retained_unit_refines (hR : R.RenamingClosed) (p : Polarity)
    {A : τ} {e : ε} {a : Term Φ 1}
    (ha : HasType F (input A) e a Silmaril.unit) (hA : Quantity.relevant ≤ quantity A)
    (he : EffectSystem.canDelete p e) :
    p.orient (fun x y => Refines (ε := ε) F R (input A) x y (product Silmaril.unit A))
      (.pair a (.bv 0)) (.pair .unit (.bv 0)) := by
  have hb := leftUnitInvDeriv (F := F) (Φ := Φ) A (⊥ : ε)
  have hbl := unitLiftDeriv hb
  have hinput : WellTyped (ε := ε) F (input A) (.let₁ a (.pair .unit (.bv 1)))
      (product Silmaril.unit A) := ⟨.let₁ (input_diagonal A hA) ha.top hbl.top⟩
  have hmid : WellTyped (ε := ε) F (input A) (.let₁ .unit (.pair .unit (.bv 1)))
      (product Silmaril.unit A) := ⟨.let₁ (inputSplit A).symm (zeroUnitDeriv A (⊤ : ε)) hbl.top⟩
  have law := DirectionalAxiom.eliminate (F := F) (p := p) (input_diagonal A hA) ha
    ((Usage.zero_le_used _).2 he) hb
  have h := Refines.directional (R := R) p law hinput hmid
  have hfirst := unit_pair_bind (R := R) hR hA ha.top
  have hlast := pureBeta (R := R) (inputSplit A) (zeroUnitDeriv A (⊥ : ε)) hbl
    (by rw [TypeQuantity.unit_quantity, zeroInput_linearity])
    (show WellTyped (ε := ε) F (input A) (.pair .unit (.bv 0)) (product Silmaril.unit A) from ⟨hb.top⟩)
  cases p with
  | positive => exact hfirst.1.trans (h.trans hlast.1)
  | negative => exact hlast.2.trans (h.trans hfirst.2)

theorem retained_elimination_refines (hR : R.RenamingClosed) (p : Polarity)
    {A B : τ} {e : ε} (a : Arrow (Φ := Φ) (ε := ε) F A B)
    (ha : HasType F (input A) e a.val B)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) :
    p.orient (fun x y => Refines (ε := ε) F R (input A) x y (product Silmaril.unit A))
      (composeArrow (copyArrow A hA) (rightArrow (composeArrow a (discardArrow B hB)) A)).val
      (leftUnitInvArrow (F := F) (ε := ε) A).val := by
  have dunit := composeDeriv ha (discardDeriv B hB e)
  have hnorm := pair_then_right (R := R) (input_diagonal A hA)
    (identityDeriv (F := F) (Φ := Φ) A (⊤ : ε)) (identityDeriv A (⊥ : ε)) dunit.top
    (by rw [input_linearity])
  have hid := identity_compose_equates R (composeArrow a (discardArrow B hB))
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hid
  have hnorm' := hnorm.trans (Equates.pair (input_diagonal A hA) hid
    (Equates.refl (R := R) ⟨identityDeriv A (⊤ : ε)⟩))
  have hstep := retained_unit_refines (R := R) hR p dunit hA he
  cases p with
  | positive =>
    simpa only [composeArrow, composeTerm, copyArrow, rightArrow, leftUnitInvArrow, discardArrow, Polarity.orient,
      continuation_atIndex] using hnorm'.1.trans hstep
  | negative =>
    simpa only [composeArrow, composeTerm, copyArrow, rightArrow, leftUnitInvArrow, discardArrow, Polarity.orient,
      continuation_atIndex] using hstep.trans hnorm'.2

theorem retained_elimination (hR : R.RenamingClosed) (p : Polarity) {A B : τ} {e : ε}
    (a : Hom (ε := ε) F R A B) (ha : hasEffect e a)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) :
    p.orient (· ≤ ·) (compose hR (copy A hA) (right hR (compose hR a (discard B hB)) A))
      (leftUnitInv A) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  exact retained_elimination_refines (R := R) hR p a da hA hB he

end Silmaril.Isotope.Refinement.Models.Syntactic
