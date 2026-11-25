module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.KnownTag.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

public section

universe u v w

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTagProofs

open LocallyNameless (Tm HasType HasTypeEffect Equiv AbortEquiv Refinement)

variable {τ : Type u} {Φ : Type v} {ε : Type w}
  [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
  {Γ : EffectCtx τ ε} {A B C : τ} {e : ε} {s p : Expr Φ}
  {ts tp : Tm Empty Φ Γ.length} {l r : Tm Empty Φ (Γ.length + 1)}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "β" => Γ.toBoundCtx

private theorem lowered_payload_wf {D : τ} (h : Wf Γ p D e) (hp : p.toLetIter Γ.length = some tp) :
    HasTypeEffect Γ₀ β tp D e := by
  obtain ⟨_, ht, hty⟩ := h.toLetIter
  exact Option.some.inj (ht.symm.trans hp) ▸ hty

theorem native_inl (h : KnownTag Γ A B e s (.inl p))
    (hs : s.toLetIter Γ.length = some ts) (hp : p.toLetIter Γ.length = some tp)
    (hl : HasTypeEffect Γ₀ (.snoc β A) l C e) (hr : HasType Φ Γ₀ (.snoc β B) r C) :
    HasTypeEffect Γ₀ β (.let₁ tp l) C e ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.case ts l r) (.let₁ tp l) C ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ ts (.case (.bv 0) l.underBinder r.underBinder)) (.let₁ tp l) C := by
  have htag : (KnownTag.injection (.inl p)).toLetIter Γ.length = some (.inl tp) := by
    simp [KnownTag.injection, Expr.toLetIter, hp]
  have hguard := h.eqv_injection.toLetIter hs htag
  have ht := lowered_payload_wf h.payload_wf hp
  have hcase := (Refinement.case hguard (Refinement.refl hl.1) (Refinement.refl hr)).trans
    (.equiv (Equiv.caseBetaL ht.1 hl.1 hr))
  exact ⟨⟨.let₁ ht.1 hl.1, sup_le ht.2 hl.2⟩, hcase,
    (Refinement.equiv (Equiv.bindCase hguard.hasType.1 hl.1 hr).symm).trans hcase⟩

theorem native_inr (h : KnownTag Γ A B e s (.inr p))
    (hs : s.toLetIter Γ.length = some ts) (hp : p.toLetIter Γ.length = some tp)
    (hl : HasType Φ Γ₀ (.snoc β A) l C) (hr : HasTypeEffect Γ₀ (.snoc β B) r C e) :
    HasTypeEffect Γ₀ β (.let₁ tp r) C e ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.case ts l r) (.let₁ tp r) C ∧
      AbortEquiv (⊥ : ε) Γ₀ β (.let₁ ts (.case (.bv 0) l.underBinder r.underBinder)) (.let₁ tp r) C := by
  have htag : (KnownTag.injection (.inr p)).toLetIter Γ.length = some (.inr tp) := by
    simp [KnownTag.injection, Expr.toLetIter, hp]
  have hguard := h.eqv_injection.toLetIter hs htag
  have ht := lowered_payload_wf h.payload_wf hp
  have hcase := (Refinement.case hguard (Refinement.refl hl) (Refinement.refl hr.1)).trans
    (.equiv (Equiv.caseBetaR ht.1 hl hr.1))
  exact ⟨⟨.let₁ ht.1 hr.1, sup_le ht.2 hr.2⟩, hcase,
    (Refinement.equiv (Equiv.bindCase hguard.hasType.1 hl hr.1).symm).trans hcase⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.KnownTagProofs
