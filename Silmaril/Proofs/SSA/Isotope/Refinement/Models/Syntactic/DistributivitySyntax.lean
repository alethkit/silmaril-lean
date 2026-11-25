module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.CaseContexts

/-! # The pure inverse distributor in native syntax -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

def distributorInvBody {n : Nat} : Term Φ (n + 2) :=
  .case (.bv 0) (.inl (.pair (.bv 2) (.bv 0))) (.inr (.pair (.bv 2) (.bv 0)))

def distributorInvTerm : Term Φ 1 := .let₂ (.bv 0) distributorInvBody

def distributorInvClosedBodyDeriv (cap : F.HasCase) (A B C : τ) (e : ε) :
    HasType F ((QCtx.nil.snoc A).snoc (coprod B C)) e (distributorInvBody : Term Φ 2)
      (coprod (product A B) (product A C)) := by
  let Γa := (QCtx.nil.snoc A).snoc (coprod B C) .zero
  let Γs := (QCtx.nil.snoc A .zero).snoc (coprod B C)
  have da := singleVariable (F := F) (Φ := Φ) Γa 1 e rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have ds := singleVariable (F := F) (Φ := Φ) Γs 0 e rfl
    (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  have hlin (D : τ) : Usage.effective (.used .linear) (quantity D) ≤
      Usage.effective (.used ⊤) (quantity D) := by
    change Quantity.linear ⊓ quantity D ≤ ⊤ ⊓ quantity D
    exact inf_le_inf bot_le le_rfl
  exact .case cap ((QCtx.Split.nil.snoc (.left (.used ⊤))).snoc (.right (.used ⊤))) ds
    (.inl cap (pairRightBindDeriv da B (.used ⊤) (hlin B)))
    (.inr cap (pairRightBindDeriv da C (.used ⊤) (hlin C)))

def distributorInvBodyDeriv {n : Nat} (cap : F.HasCase) (Γ : QCtx τ n) (hd : Γ.Discardable)
    (A B C : τ) (e : ε) :
    HasType F ((Γ.snoc A).snoc (coprod B C)) e (distributorInvBody : Term Φ (n + 2))
      (coprod (product A B) (product A C)) :=
  (distributorInvClosedBodyDeriv cap A B C e).rename _
    (((QCtx.Weakening.empty Γ hd).up A).up (coprod B C))

def distributorInvDeriv (cap : F.HasCase) (A B C : τ) (e : ε) :
    HasType F (input (product A (coprod B C))) e (distributorInvTerm : Term Φ 1)
      (coprod (product A B) (product A C)) := by
  let P := product A (coprod B C)
  have hz : (QCtx.nil.snoc P .zero).Discardable := by
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact le_rfl
  exact .let₂ (inputSplit P) (identityDeriv P e)
    (distributorInvBodyDeriv cap _ hz A B C e)

def distributorInvArrow (cap : F.HasCase) (A B C : τ) :
    Arrow (Φ := Φ) (ε := ε) F (product A (coprod B C))
      (coprod (product A B) (product A C)) :=
  ⟨distributorInvTerm, ⟨distributorInvDeriv cap A B C ⊤⟩⟩

def distributorInv (cap : F.HasCase) (A B C : τ) :
    Hom (ε := ε) F R (product A (coprod B C)) (coprod (product A B) (product A C)) :=
  ofArrow (distributorInvArrow cap A B C)

theorem distributorInv_pure (cap : F.HasCase) (A B C : τ) :
    hasEffect (⊥ : ε) (distributorInv (R := R) cap A B C) :=
  ⟨distributorInvArrow cap A B C, rfl, ⟨distributorInvDeriv cap A B C ⊥⟩⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
