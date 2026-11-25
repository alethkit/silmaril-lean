module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Associator
public import Silmaril.Raw.SSA.Isotope.Refinement.TypingSubstitution

/-! # Quantitative beta helpers for structural categorical equations -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n} {b : Term Φ (n + 1)}
variable {A B : τ} {e : ε}

/-- Pure beta is an equation when the replacement resources support the bound type.
Endpoint formation is explicit, matching the corrected written beta rule. -/
theorem pureBeta (split : Γ.Split Γl Γr) (ha : HasType F Γl (⊥ : ε) a A)
    (hb : HasType F (Γr.snoc A) e b B) (hq : quantity A ≤ Γl.linearity)
    (hout : WellTyped (ε := ε) F Γ (Tm.instantiate b a) B) :
    Equates (ε := ε) F R Γ (.let₁ a b) (Tm.instantiate b a) B := by
  have law (p : Polarity) : DirectionalAxiom (ε := ε) F p Γ
      (.let₁ a b) (Tm.instantiate b a) B :=
    .beta split ha hb.normalizeBinder hb (EffectSystem.pure_moves p e)
      (by simpa only [EffectSystem.quantity_pure, inf_top_eq, Usage.used_le_used] using hq)
  have hin : WellTyped (ε := ε) F Γ (.let₁ a b) B := ⟨.let₁ split.symm ha.top hb.top⟩
  exact ⟨.directional .positive (law _) hin hout, .directional .negative (law _) hin hout⟩

/-- A linear use can substitute an arbitrary computation when it commutes with the body. -/
theorem linearBeta {η : ε} (split : Γ.Split Γl Γr) (ha : HasType F Γl e a A)
    (hb : HasType F (Γr.snoc A (.used .linear)) η b B)
    (hbDefault : HasType F (Γr.snoc A) η b B) (hm : EffectSystem.commutes e η)
    (hout : WellTyped (ε := ε) F Γ (Tm.instantiate b a) B) :
    Equates (ε := ε) F R Γ (.let₁ a b) (Tm.instantiate b a) B := by
  have law (p : Polarity) : DirectionalAxiom (ε := ε) F p Γ
      (.let₁ a b) (Tm.instantiate b a) B :=
    .beta split ha hb hbDefault (by cases p; exact hm.1; exact hm.2)
      ((Usage.used_le_used _ _).2 bot_le)
  have hin : WellTyped (ε := ε) F Γ (.let₁ a b) B := ⟨.let₁ split.symm ha.top hbDefault.top⟩
  exact ⟨.directional .positive (law _) hin hout, .directional .negative (law _) hin hout⟩

end Silmaril.Isotope.Refinement.Models.Syntactic

namespace Silmaril.Isotope.Refinement.Equates

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable {n : Nat} {Γ Γl Γr : QCtx τ n} {a a' b b' : Term Φ n} {A B C : τ}

theorem let₁ {c c' : Term Φ (n + 1)} (split : Γ.Split Γl Γr)
    (ha : Equates (ε := ε) F R Γr a a' A)
    (hc : Equates (ε := ε) F R (Γl.snoc A) c c' B) :
    Equates (ε := ε) F R Γ (.let₁ a c) (.let₁ a' c') B :=
  ⟨.let₁ split ha.1 hc.1, .let₁ split ha.2 hc.2⟩

theorem let₂ {c c' : Term Φ (n + 2)} (split : Γ.Split Γl Γr)
    (ha : Equates (ε := ε) F R Γr a a' (product A B))
    (hc : Equates (ε := ε) F R ((Γl.snoc A).snoc B) c c' C) :
    Equates (ε := ε) F R Γ (.let₂ a c) (.let₂ a' c') C :=
  ⟨.let₂ split ha.1 hc.1, .let₂ split ha.2 hc.2⟩

theorem pair (split : Γ.Split Γl Γr)
    (ha : Equates (ε := ε) F R Γl a a' A)
    (hb : Equates (ε := ε) F R Γr b b' B) :
    Equates (ε := ε) F R Γ (.pair a b) (.pair a' b') (product A B) :=
  ⟨.pair split ha.1 hb.1, .pair split ha.2 hb.2⟩

end Silmaril.Isotope.Refinement.Equates

namespace Silmaril.Isotope.Refinement.QCtx

variable {τ : Type u} [HasQuantity τ]

/-- A discardable context can weaken the empty context without inventing resources. -/
theorem Weakening.empty {n : Nat} (Γ : QCtx τ n) (hd : Γ.Discardable) :
    Weakening Γ QCtx.nil (Fin.elim0 : Fin 0 → Fin n) :=
  discardable_iff_weakening_nil.mp hd

end Silmaril.Isotope.Refinement.QCtx

namespace Silmaril.Isotope.Refinement.Models.Syntactic

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {n : Nat}

/-- Product parameters can be reassembled above any discardable old context. -/
def parametersDeriv (Γ : QCtx τ n) (hd : Γ.Discardable) (A B : τ) (e : ε) :
    HasType F ((Γ.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ (n + 2)) (product A B) := by
  have d : HasType F ((QCtx.nil.snoc A).snoc B) e (.pair (.bv 1) (.bv 0) : Term Φ 2)
      (product A B) :=
    .pair ((QCtx.Split.nil.snoc (.left (.used ⊤))).snoc (.right (.used ⊤)))
      (singleVariable ((QCtx.nil.snoc A).snoc B .zero) 1 e rfl
        (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl))
      (singleVariable ((QCtx.nil.snoc A .zero).snoc B) 0 e rfl
        (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl))
  exact d.rename _ (((QCtx.Weakening.empty Γ hd).up A).up B)

/-- The swapped product parameters also use each newly bound component once. -/
def swapParametersDeriv (Γ : QCtx τ n) (hd : Γ.Discardable) (A B : τ) (e : ε) :
    HasType F ((Γ.snoc A).snoc B) e (.pair (.bv 0) (.bv 1) : Term Φ (n + 2)) (product B A) := by
  have d : HasType F ((QCtx.nil.snoc A).snoc B) e (.pair (.bv 0) (.bv 1) : Term Φ 2)
      (product B A) :=
    .pair ((QCtx.Split.nil.snoc (.left (.used ⊤))).snoc (.right (.used ⊤))).symm
      (singleVariable ((QCtx.nil.snoc A .zero).snoc B) 0 e rfl
        (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl))
      (singleVariable ((QCtx.nil.snoc A).snoc B .zero) 1 e rfl
        (by intro j hj; fin_cases j <;> first | exact False.elim (hj rfl) | rfl))
  exact d.rename _ (((QCtx.Weakening.empty Γ hd).up A).up B)

end Silmaril.Isotope.Refinement.Models.Syntactic
