module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Instantiation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.TensorSyntax

/-! # Resource-aware commuting conversions for product binders -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}
variable {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n} {e : ε}
variable {a : Term Φ n} {b : Term Φ (n + 2)} {c : Term Φ (n + 1)}
variable {A B C D E : τ}

theorem underTwoBinders_asRename (b : Term Φ (n + 2)) :
    b.underTwoBinders = Tm.rename (Tm.up (Tm.up (Fin.succ : Fin n → Fin (n + 1)))) b := by
  apply Tm.rename_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

def pairContinuation (b : Term Φ (n + 2)) : Term Φ (n + 1) :=
  .let₂ (.bv 0) b.underTwoBinders

def pairContinuationDeriv (hb : HasType F ((Γ.snoc A).snoc B) e b C) :
    HasType F (Γ.snoc (product A B)) e (pairContinuation b) C := by
  apply HasType.let₂ ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (atZeroDeriv Γ (identityDeriv _ e))
  simpa only [underTwoBinders_asRename] using
    (hb.rename _ (((QCtx.Weakening.insertZero Γ (product A B)).up A).up B))

/-- Product elimination factors through an ordinary let, with the whole pair unused after unpacking. -/
theorem pair_bind (split : Γ.Split Γl Γr)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γl.snoc A).snoc B) (⊤ : ε) b C) :
    Equates (ε := ε) F R Γ (.let₂ a b) (.let₁ a (pairContinuation b)) C :=
  Equates.ofAxiom (.pairBind split ha hb) ⟨.let₂ split ha hb⟩
    ⟨.let₁ split ha (pairContinuationDeriv hb)⟩

/-- Inserting two unused earlier binders into a one-parameter continuation. -/
def underPairDeriv (hc : HasType F (Γ.snoc C) e c D) (A B : τ) :
    HasType F (((Γ.snoc A .zero).snoc B .zero).snoc C) e c.underBinder.underBinder D :=
  (hc.rename _ ((QCtx.Weakening.insertZero Γ A).up C)).rename _
    ((QCtx.Weakening.insertZero (Γ.snoc A .zero) B).up C)

/-- Ordinary composition moves under a product binder with its exact quantitative reassociation. -/
theorem let_pair (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γm.snoc A).snoc B) (⊤ : ε) b C)
    (hc : HasType F (Γl.snoc C) (⊤ : ε) c D) :
    Equates (ε := ε) F R Γ (.let₁ (.let₂ a b) c)
      (.let₂ a (.let₁ b c.underBinder.underBinder)) D := by
  obtain ⟨Γmr, hsplit, hmr⟩ := outer.swapAssoc inner.symm
  exact Equates.ofAxiom (.letLetPair outer inner ha hb hc)
    ⟨.let₁ hsplit.symm (.let₂ hmr ha hb) hc⟩
    ⟨.let₂ outer ha (.let₁ ((inner.snoc (.right (.used ⊤))).snoc (.right (.used ⊤))) hb
      (underPairDeriv hc A B))⟩

/-- Inserting two unused earlier variables into a two-parameter continuation. -/
def underPair₂Deriv {c : Term Φ (n + 2)}
    (hc : HasType F ((Γ.snoc C).snoc D) e c E) (A B : τ) :
    HasType F ((((Γ.snoc A .zero).snoc B .zero).snoc C).snoc D) e
      c.underTwoBinders.underTwoBinders E := by
  simpa only [underTwoBinders_asRename] using
    ((hc.rename _ (((QCtx.Weakening.insertZero Γ A).up C).up D)).rename _
    (((QCtx.Weakening.insertZero (Γ.snoc A .zero) B).up C).up D))

theorem pairContinuation_underPair (c : Term Φ (n + 2)) :
    (pairContinuation c).underBinder.underBinder =
      pairContinuation c.underTwoBinders.underTwoBinders := by
  simp only [pairContinuation, Tm.underBinder, Tm.underTwoBinders, Tm.rename, Tm.rename_comp]
  congr 1
  apply Tm.rename_congr
  intro i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

/-- Product elimination moves through product elimination; all old resources
are assigned by the two displayed splits. -/
theorem pair_pair {c : Term Φ (n + 2)}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γr (⊤ : ε) a (product A B))
    (hb : HasType F ((Γm.snoc A).snoc B) (⊤ : ε) b (product C D))
    (hc : HasType F ((Γl.snoc C).snoc D) (⊤ : ε) c E) :
    Equates (ε := ε) F R Γ (.let₂ (.let₂ a b) c)
      (.let₂ a (.let₂ b c.underTwoBinders.underTwoBinders)) E := by
  obtain ⟨Γmr, hsplit, hmr⟩ := outer.swapAssoc inner.symm
  have hfirst := pair_bind (R := R) hsplit.symm (.let₂ hmr ha hb) hc
  have hmiddle := let_pair (R := R) outer inner ha hb (pairContinuationDeriv hc)
  have hlast := pair_bind (R := R)
    ((inner.snoc (.right (.used ⊤))).snoc (.right (.used ⊤))) hb (underPair₂Deriv hc A B)
  apply hfirst.trans
  apply hmiddle.trans
  rw [pairContinuation_underPair]
  exact Equates.let₂ outer (Equates.refl ⟨ha⟩) hlast.symm

end Silmaril.Isotope.Refinement.Models.Syntactic
