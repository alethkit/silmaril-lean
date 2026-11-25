module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Action

/-! # Resource-aware case congruence and reductions -/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement

open LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ}

theorem Equates.inl {n : Nat} {Γ : QCtx τ n} {a b : Term Φ n} {A B : τ}
    (cap : F.HasCase) (h : Equates (ε := ε) F R Γ a b A) :
    Equates (ε := ε) F R Γ (.inl a) (.inl b) (coprod A B) :=
  ⟨.inl cap h.1, .inl cap h.2⟩

theorem Equates.inr {n : Nat} {Γ : QCtx τ n} {a b : Term Φ n} {A B : τ}
    (cap : F.HasCase) (h : Equates (ε := ε) F R Γ a b B) :
    Equates (ε := ε) F R Γ (.inr a) (.inr b) (coprod A B) :=
  ⟨.inr cap h.1, .inr cap h.2⟩

theorem Equates.case {n : Nat} {Γ Γl Γr : QCtx τ n}
    {a a' : Term Φ n} {l l' r r' : Term Φ (n + 1)} {A B C : τ}
    (cap : F.HasCase) (split : Γ.Split Γl Γr)
    (ha : Equates (ε := ε) F R Γr a a' (coprod A B))
    (hl : Equates (ε := ε) F R (Γl.snoc A) l l' C)
    (hr : Equates (ε := ε) F R (Γl.snoc B) r r' C) :
    Equates (ε := ε) F R Γ (.case a l r) (.case a' l' r') C :=
  ⟨.case cap split ha.1 hl.1 hr.1, .case cap split ha.2 hl.2 hr.2⟩

namespace Models.Syntactic

def caseContinuation {n : Nat} (l r : Term Φ (n + 1)) : Term Φ (n + 1) :=
  .case (.bv 0) l.underBinder r.underBinder

def caseContinuationDeriv {n : Nat} {Γ : QCtx τ n} {e : ε}
    {l r : Term Φ (n + 1)} {A B C : τ} (cap : F.HasCase)
    (hl : HasType F (Γ.snoc A) e l C) (hr : HasType F (Γ.snoc B) e r C) :
    HasType F (Γ.snoc (coprod A B)) e (caseContinuation l r) C :=
  .case cap ((QCtx.Split.zero_right Γ).snoc (.right (.used ⊤)))
    (atZeroDeriv Γ (identityDeriv _ e))
    (hl.rename _ ((QCtx.Weakening.insertZero Γ (coprod A B)).up A))
    (hr.rename _ ((QCtx.Weakening.insertZero Γ (coprod A B)).up B))

theorem case_bind {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n}
    {l r : Term Φ (n + 1)} {A B C : τ} (cap : F.HasCase)
    (split : Γ.Split Γl Γr) (ha : HasType F Γr (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C) :
    Equates (ε := ε) F R Γ (.case a l r) (.let₁ a (caseContinuation l r)) C :=
  Equates.ofAxiom (.caseBind cap split ha hl hr) ⟨.case cap split ha hl hr⟩
    ⟨.let₁ split ha (caseContinuationDeriv cap hl hr)⟩

/-- Sequential execution after a case moves into both branches. -/
theorem let_case {n : Nat} {Γ Γl Γm Γr Γc : QCtx τ n}
    {a : Term Φ n} {l r d : Term Φ (n + 1)} {A B C D : τ}
    (cap : F.HasCase) (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γm)
    (ha : HasType F Γm (⊤ : ε) a (coprod A B))
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C)
    (hd : HasType F (Γr.snoc C) (⊤ : ε) d D) :
    Equates (ε := ε) F R Γ (.let₁ (.case a l r) d)
      (.case a (.let₁ l d.underBinder) (.let₁ r d.underBinder)) D := by
  obtain ⟨Γlr, whole, lr⟩ := outer.swapAssoc inner
  exact Equates.ofAxiom (.letCase cap outer inner ha hl hr hd)
    ⟨.let₁ outer.symm (.case cap inner ha hl hr) hd⟩
    ⟨.case cap whole ha
      (.let₁ (lr.symm.snoc (.right (.used ⊤))) hl
        (hd.rename _ ((QCtx.Weakening.insertZero Γr A).up C)))
      (.let₁ (lr.symm.snoc (.right (.used ⊤))) hr
        (hd.rename _ ((QCtx.Weakening.insertZero Γr B).up C)))⟩

theorem pureCaseBetaL {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n}
    {l r : Term Φ (n + 1)} {A B C : τ} (cap : F.HasCase)
    (split : Γ.Split Γl Γr) (ha : HasType F Γr (⊥ : ε) a A)
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C) (hq : quantity A ≤ Γr.linearity) :
    Equates (ε := ε) F R Γ (.case (.inl a) l r) (Tm.instantiate l a) C :=
  (Equates.ofAxiom (.caseBetaL cap split ha.top hl hr)
    ⟨.case cap split (.inl cap ha.top) hl hr⟩ ⟨.let₁ split ha.top hl⟩).trans
    (pureBetaTyped split.symm ha hl hq)

theorem pureCaseBetaR {n : Nat} {Γ Γl Γr : QCtx τ n} {a : Term Φ n}
    {l r : Term Φ (n + 1)} {A B C : τ} (cap : F.HasCase)
    (split : Γ.Split Γl Γr) (ha : HasType F Γr (⊥ : ε) a B)
    (hl : HasType F (Γl.snoc A) (⊤ : ε) l C)
    (hr : HasType F (Γl.snoc B) (⊤ : ε) r C) (hq : quantity B ≤ Γr.linearity) :
    Equates (ε := ε) F R Γ (.case (.inr a) l r) (Tm.instantiate r a) C :=
  (Equates.ofAxiom (.caseBetaR cap split ha.top hl hr)
    ⟨.case cap split (.inr cap ha.top) hl hr⟩ ⟨.let₁ split ha.top hr⟩).trans
    (pureBetaTyped split.symm ha hr hq)

end Models.Syntactic
end Silmaril.Isotope.Refinement
