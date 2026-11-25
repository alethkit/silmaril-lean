module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CopyDiscard

/-! # Directed copy naturality from quantitative beta -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- Copying the fresh parameter requires precisely its effective relevance. -/
def copyBodyDeriv {n : Nat} (Γ : QCtx τ n) (A : τ) (q : Usage) (e : ε)
    (hq : Usage.used .relevant ≤ Usage.effective q (quantity A)) :
    HasType F (Γ.zero.snoc A q) e (.pair (.bv 0) (.bv 0) : Term Φ (n + 1)) (product A A) := by
  have hz : Γ.zero.Split Γ.zero Γ.zero := fun _ => ⟨rfl, rfl, .left .zero⟩
  have hl : Usage.effective (.used .linear) (quantity A) ≤ Usage.effective q (quantity A) := by
    rw [Usage.effective_linear]
    exact ((Usage.used_le_used _ _).2 bot_le).trans hq
  exact .pair (hz.snoc (.both q hq)) (zeroParameter Γ A q e hl) (zeroParameter Γ A q e hl)

/-- Duplicating an effectful computation has the polarity prescribed by its
effect allowance. The two copies retain their left-to-right execution order. -/
theorem copy_natural_refines (p : Polarity) {A B : τ} {e : ε}
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (ha : HasType F (input A) e a.val B)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (he : EffectSystem.canCopy p e) :
    p.orient (fun x y => Refines (ε := ε) F R (input A) x y (product B B))
      (composeArrow a (copyArrow B hB)).val
      (composeArrow (copyArrow A hA) (composeArrow (rightArrow a A) (leftArrow B a))).val := by
  have hr : Usage.used .relevant ≤ Usage.effective (.used .relevant) (quantity B) := by
    simp only [Usage.effective, Usage.used_mul_used, Usage.used_le_used]
    exact le_inf le_rfl hB
  have ht : Usage.used .relevant ≤ Usage.effective (.used ⊤) (quantity B) := by
    simpa only [Usage.effective, Usage.used_mul_used, top_inf_eq, Usage.used_le_used] using hB
  have hb := copyBodyDeriv (F := F) (Φ := Φ) (input A) B (.used .relevant) (⊥ : ε) hr
  have hbDefault := copyBodyDeriv (F := F) (Φ := Φ) (input A) B (.used ⊤) (⊥ : ε) ht
  have hz : (input A).zero = QCtx.nil.snoc A .zero := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    rfl
  rw [hz] at hb hbDefault
  have hu : Usage.used .relevant ≤ Usage.used ((input A).linearity ⊓ EffectSystem.quantity p e) := by
    rw [Usage.used_le_used, input_linearity]
    exact le_inf hA he
  have law := DirectionalAxiom.beta (F := F) (p := p) (inputSplit A).symm
    ha hb hbDefault (EffectSystem.moves_pure p e) hu
  have h : Refines (ε := ε) F R (input A)
      (p.source (.let₁ a.val (.pair (.bv 0) (.bv 0))) (.pair a.val a.val))
      (p.target (.let₁ a.val (.pair (.bv 0) (.bv 0))) (.pair a.val a.val)) (product B B) :=
    .directional p law (composeArrow a (copyArrow B hB)).property
      ⟨.pair (input_diagonal A hA) ha.top ha.top⟩
  have hn := copy_tensor_equates (R := R) hA a a
  cases p with
  | positive => exact h.trans hn.2
  | negative => exact hn.1.trans h

theorem copy_natural (hR : R.RenamingClosed) (p : Polarity) {A B : τ} {e : ε}
    (a : Hom (ε := ε) F R A B) (ha : hasEffect e a)
    (hA : Quantity.relevant ≤ quantity A) (hB : Quantity.relevant ≤ quantity B)
    (he : EffectSystem.canCopy p e) :
    p.orient (· ≤ ·) (compose hR a (copy B hB))
      (compose hR (copy A hA) (compose hR (right hR a A) (left hR B a))) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  exact copy_natural_refines p a da hA hB he

end Silmaril.Isotope.Refinement.Models.Syntactic
