module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Premonoidal
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Action

/-! # Native quantity-sensitive copy and discard equations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem input_diagonal (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    (input A).Split (input A) (input A) :=
  QCtx.Split.nil.snoc (.both (.used ⊤) (by
    simpa only [Usage.effective, Usage.used_mul_used, top_inf_eq, Usage.used_le_used] using hA))

theorem copy_comm_equates (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    Equates (ε := ε) F R (input A)
      (composeArrow (copyArrow (F := F) (ε := ε) A hA) (swapArrow A A)).val
      (copyArrow (F := F) (ε := ε) A hA).val (product A A) := by
  have h := pair_then_swap (R := R) (input_diagonal A hA)
    (identityDeriv (F := F) (Φ := Φ) A (⊥ : ε)) (identityDeriv A (⊤ : ε))
    (by rw [input_linearity])
  simpa only [composeArrow, composeTerm, copyArrow, continuation_atIndex] using h

theorem copy_comm (hR : R.RenamingClosed) (A : τ) (hA : Quantity.relevant ≤ quantity A) :
    compose (ε := ε) (F := F) (R := R) hR (copy A hA) (swap A A) = copy A hA :=
  Quotient.sound (copy_comm_equates A hA)

theorem discard_unit (h : Quantity.affine ≤ quantity (Silmaril.unit : τ)) :
    discard (ε := ε) (F := F) (R := R) Silmaril.unit h = identity Silmaril.unit :=
  Quotient.sound (unitVariable_equates (ε := ε) (F := F) (R := R)).symm

theorem copy_unit (h : Quantity.relevant ≤ quantity (Silmaril.unit : τ)) :
    copy (ε := ε) (F := F) (R := R) Silmaril.unit h = leftUnitInv Silmaril.unit := by
  apply Quotient.sound
  exact Equates.pair (input_diagonal Silmaril.unit h)
    (unitVariable_equates (ε := ε) (F := F) (R := R))
    (Equates.refl (R := R) ⟨identityDeriv Silmaril.unit (⊤ : ε)⟩)

/-- Directed discard naturality is exactly the zero-use beta rule. -/
theorem discard_natural_refines (p : Polarity) {A B : τ} {e : ε}
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (ha : HasType F (input A) e a.val B)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) :
    p.orient (fun x y => Refines (ε := ε) F R (input A) x y Silmaril.unit)
      (composeArrow a (discardArrow B hB)).val (discardArrow (F := F) (ε := ε) A hA).val := by
  have hb : HasType F ((QCtx.nil.snoc A .zero).snoc B .zero) (⊥ : ε) (.unit : Term Φ 2) Silmaril.unit :=
    .unit (by intro i; fin_cases i <;> exact le_rfl)
  have hbDefault := (discardDeriv (F := F) (Φ := Φ) B hB (⊥ : ε)).rename _
    ((QCtx.Weakening.insertZero QCtx.nil A).up B)
  have hu : Usage.zero ≤ Usage.used ((input A).linearity ⊓ EffectSystem.quantity p e) := by
    rw [Usage.zero_le_used, input_linearity]
    exact le_inf hA he
  have h := Refines.directional (R := R) p
    (DirectionalAxiom.beta (inputSplit A).symm ha hb hbDefault (EffectSystem.moves_pure p e) hu)
    (composeArrow a (discardArrow B hB)).property (discardArrow (F := F) (ε := ε) A hA).property
  cases p <;> exact h

theorem discard_natural (hR : R.RenamingClosed) (p : Polarity) {A B : τ} {e : ε}
    (a : Hom (ε := ε) F R A B) (ha : hasEffect e a)
    (hA : Quantity.affine ≤ quantity A) (hB : Quantity.affine ≤ quantity B)
    (he : EffectSystem.canDelete p e) :
    p.orient (· ≤ ·) (compose hR a (discard B hB)) (discard A hA) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  exact discard_natural_refines p a da hA hB he

/-- Sequential tensor after a diagonal computes both copies in their stated
left-to-right order. This normalization makes no copying-effect assumption. -/
theorem copy_tensor_equates {A B C : τ} (hA : Quantity.relevant ≤ quantity A)
    (f : Arrow (Φ := Φ) (ε := ε) F A B) (g : Arrow (Φ := Φ) (ε := ε) F A C) :
    Equates (ε := ε) F R (input A)
      (composeArrow (copyArrow A hA) (composeArrow (rightArrow f A) (leftArrow B g))).val
      (.pair f.val g.val) (product B C) := by
  obtain ⟨df⟩ := f.property
  obtain ⟨dg⟩ := g.property
  have di := identityDeriv (F := F) (Φ := Φ) A (⊥ : ε)
  have hf := pair_then_right (R := R) (input_diagonal A hA) di.top di df (by rw [input_linearity])
  have hidf := identity_compose_equates (ε := ε) (F := F) R f
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hidf
  have hf' := hf.trans (Equates.pair (input_diagonal A hA) hidf (Equates.refl ⟨di.top⟩))
  have hg := pair_then_left_any (R := R) (input_diagonal A hA) df di.top dg
  have hidg := identity_compose_equates (ε := ε) (F := F) R g
  simp only [composeArrow, composeTerm, identityArrow, continuation_atIndex] at hidg
  have hg' := hg.trans (Equates.pair (input_diagonal A hA) (Equates.refl ⟨df⟩) hidg)
  have h := (action_compose (R := R) (copyDeriv A hA (⊤ : ε))
    (rightDeriv A df) (leftDeriv B dg)).trans
    ((action_congr hf' (leftDeriv B dg)).trans hg')
  simpa only [composeArrow, composeTerm, copyArrow, rightArrow, leftArrow,
    continuation_atIndex, action] using h

end Silmaril.Isotope.Refinement.Models.Syntactic
