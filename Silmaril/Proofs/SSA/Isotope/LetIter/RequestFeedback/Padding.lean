module

public import Silmaril.SSA.Isotope.LetIter.RequestFeedback.Defs

public section

open Silmaril Silmaril.Isotope

namespace Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback.Proofs

universe u v w r

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ν : Type w} [DecidableEq ν] {ε : Type r} [HasEff Φ ε]
  {n : Nat} {Γ : Ctx ν τ} {β : BoundCtx τ n} {f : Φ}
  {init : Tm ν Φ n} {R : τ} {pe : ε}

private theorem pair_first {C : τ} :
    Equiv pe Γ (β.snoc C)
      (.let₂ (.pair (.bv 0) .unit) (.bv 1) : Tm ν Φ (n + 1)) (.bv 0) C := by
  have project := Equiv.pairBeta (pureEff := pe) (Γ := Γ) (β := β.snoc C)
    (HasType.bv (Φ := Φ) (ι := 0)) HasType.unit
    (HasType.bv (ι := 1) :
      HasType Φ Γ (((β.snoc C).snoc C).snoc (unit : τ)) (.bv 1) C)
  exact project.trans ((Equiv.let₁ (.refl .bv) (Equiv.letBeta .unit .unit .bv)).trans
    (Equiv.letEta .bv))

theorem remove_unit (hout : instrTrg f = coprod R (instrSrc f))
    (ha : HasType Φ Γ β init (instrSrc f)) :
    Equiv pe Γ β (padded f init) (loop f init) R := by
  let S : τ := instrSrc f
  let U := product S (unit : τ)
  have thin : HasType Φ Γ (β.snoc S) (.op f (.bv 0)) (coprod R S) := hout ▸ HasType.op .bv
  have paddedRequest : HasType Φ Γ (β.snoc U) (.op f (.let₂ (.bv 0) (.bv 1))) (coprod R S) :=
    hout ▸ HasType.op (.let₂ .bv .bv)
  have body : HasType Φ Γ (β.snoc U) (paddedBody f n) (coprod R U) :=
    .case paddedRequest (.inl .bv) (.inr (.pair .bv .unit))
  have square : Equiv pe Γ (β.snoc S)
      (.case (.op f (.bv 0)) (.inl (.bv 0)) (.inr (Tm.underBinder (.pair (.bv 0) .unit))))
      (Tm.instantiate (Tm.underBinder (paddedBody f n)) (.pair (.bv 0) .unit)) (coprod R U) := by
    change Equiv pe Γ (β.snoc S)
      (.case (.op f (.bv 0)) (.inl (.bv 0)) (.inr (.pair (.bv 0) .unit)))
      (.case (.op f (.let₂ (.pair (.bv 0) .unit) (.bv 1))) (.inl (.bv 0)) (.inr (.pair (.bv 0) .unit)))
      (coprod R U)
    have req : Equiv pe Γ (β.snoc S)
        (.op f (.let₂ (.pair (.bv 0) .unit) (.bv 1))) (.op f (.bv 0)) (coprod R S) :=
      hout ▸ Equiv.op (f := f) (pair_first (C := S))
    exact .case req.symm (.inl (.refl .bv)) (.inr (.pair (.refl .bv) .unit))
  have padding : HasType Φ Γ (β.snoc S) (.pair (.bv 0) .unit) U := .pair .bv .unit
  exact (Equiv.uniformity ha padding (.pair .bv .unit) thin body square).symm

omit [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν] in
theorem effect_eq [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε]
    (f : Φ) (init : Tm ν Φ n) : (padded f init).effect = ((loop f init).effect : ε) :=
by
  simp [Tm.effect]

theorem remove_unit_at_bound [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}
    (hout : instrTrg f = coprod R (instrSrc f))
    (ha : HasType Φ Γ β init (instrSrc f)) (he : HasEffect (loop f init) e) :
    HasTypeEffect Γ β (padded f init) R e ∧ HasTypeEffect Γ β (loop f init) R e ∧
      Equiv (⊥ : ε) Γ β (padded f init) (loop f init) R := by
  have eq : Equiv (⊥ : ε) Γ β (padded f init) (loop f init) R := remove_unit hout ha
  have paddedEffect : HasEffect (padded f init) e := by
    unfold HasEffect at he ⊢
    rwa [effect_eq (ε := ε) f init]
  exact ⟨⟨eq.hasType.1, paddedEffect⟩, ⟨eq.hasType.2, he⟩, eq⟩

end Silmaril.Isotope.LetIter.LocallyNameless.RequestFeedback.Proofs
