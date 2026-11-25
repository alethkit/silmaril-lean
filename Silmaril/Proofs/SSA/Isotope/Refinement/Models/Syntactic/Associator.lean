module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Coherence
public import Mathlib.Tactic.FinCases

/-! # Associator representatives with quantitative typing -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

/-- A selected full annotation consumes a variable once; every other slot is unused. -/
def singleVariable {n : Nat} (Γ : QCtx τ n) (i : Fin n) (e : ε)
    (hi : (Γ i).2 = .used ⊤) (hz : ∀ j, j ≠ i → (Γ j).2 = .zero) :
    HasType F Γ e (.bv i : Term Φ n) (Γ i).1 := by
  apply HasType.var
  constructor
  · simp only [QCtx.effective, Usage.effective, hi, Usage.used_mul_used, top_inf_eq,
      Usage.used_le_used]
    exact inf_le_right
  · intro j hj
    simp only [QCtx.effective, Usage.effective, hz j hj, Usage.zero_mul]
    exact le_rfl

def assocTerm : Term Φ 1 :=
  .let₂ (.bv 0) (.let₂ (.bv 1) (.pair (.bv 1) (.pair (.bv 0) (.bv 2))))

def assocInvTerm : Term Φ 1 :=
  .let₂ (.bv 0) (.let₂ (.bv 0) (.pair (.pair (.bv 3) (.bv 1)) (.bv 0)))

/-- Reassociation never copies or discards any product component. -/
def assocDeriv (A B C : τ) (e : ε) :
    HasType F (input (product (product A B) C)) e (assocTerm (Φ := Φ)) (product A (product B C)) := by
  let P := product (product A B) C
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A).snoc B .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C .zero).snoc A .zero).snoc B
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc (product A B) .zero).snoc C).snoc A .zero).snoc B .zero
  apply HasType.let₂ (inputSplit _) (identityDeriv _ _)
  apply HasType.let₂ (pairSplit P (product A B) C).symm (leftParameter _ _ _ _)
  apply HasType.pair
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
      (.right (.used ⊤))).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · exact singleVariable Γa 1 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  · apply HasType.pair
      (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left .zero)).snoc
        (.right (.used ⊤))).snoc (.left .zero)).snoc (.left (.used ⊤)))
    · exact singleVariable Γb 0 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
    · exact singleVariable Γc 2 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)

def assocInvDeriv (A B C : τ) (e : ε) :
    HasType F (input (product A (product B C))) e (assocInvTerm (Φ := Φ)) (product (product A B) C) := by
  let P := product A (product B C)
  let Γa : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A).snoc (product B C) .zero).snoc B .zero).snoc C .zero
  let Γb : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B).snoc C .zero
  let Γc : QCtx τ 5 := ((((QCtx.nil.snoc P .zero).snoc A .zero).snoc (product B C) .zero).snoc B .zero).snoc C
  apply HasType.let₂ (inputSplit _) (identityDeriv _ _)
  apply HasType.let₂ (pairSplit P A (product B C)) (rightParameter _ _ _ _)
  apply HasType.pair
    (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
      (.left .zero)).snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
  · apply HasType.pair
      (((((QCtx.Split.nil.snoc (.left .zero)).snoc (.left (.used ⊤))).snoc
        (.left .zero)).snoc (.right (.used ⊤))).snoc (.left .zero))
    · exact singleVariable Γa 3 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
    · exact singleVariable Γb 1 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)
  · exact singleVariable Γc 0 e rfl (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl)

def assocArrow (A B C : τ) :
    Arrow (Φ := Φ) (ε := ε) F (product (product A B) C) (product A (product B C)) :=
  ⟨assocTerm, ⟨assocDeriv A B C ⊤⟩⟩

def assocInvArrow (A B C : τ) :
    Arrow (Φ := Φ) (ε := ε) F (product A (product B C)) (product (product A B) C) :=
  ⟨assocInvTerm, ⟨assocInvDeriv A B C ⊤⟩⟩

def assoc (A B C : τ) : Hom (ε := ε) F R (product (product A B) C) (product A (product B C)) :=
  ofArrow (assocArrow A B C)

def assocInv (A B C : τ) : Hom (ε := ε) F R (product A (product B C)) (product (product A B) C) :=
  ofArrow (assocInvArrow A B C)

theorem assoc_pure (A B C : τ) : hasEffect (⊥ : ε) (assoc (F := F) (R := R) A B C) :=
  ⟨assocArrow A B C, rfl, ⟨assocDeriv A B C ⊥⟩⟩

theorem assocInv_pure (A B C : τ) : hasEffect (⊥ : ε) (assocInv (F := F) (R := R) A B C) :=
  ⟨assocInvArrow A B C, rfl, ⟨assocInvDeriv A B C ⊥⟩⟩

end Silmaril.Isotope.Refinement.Models.Syntactic
