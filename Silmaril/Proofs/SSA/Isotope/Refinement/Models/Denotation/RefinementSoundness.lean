module

public import Silmaril.SSA.Isotope.Refinement.Models.Defs
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.WitnessCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.OrderedInterpretation

/-! # From primitive rule soundness to full native refinement soundness -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqModel.{u,v,w,r} τ Φ ε) {F : Fragment} (K : ControlData M.toSeqData F)

/-- A proved semantic comparison can use any typing witnesses at its endpoints. -/
theorem le_of_coherent (H : WitnessCoherent M K)
    {n : Nat} {Γ : QCtx τ n} {a b : Term Φ n} {A : τ} {e η e' η' : ε}
    (ha : HasType F Γ e a A) (hb : HasType F Γ η b A)
    (h : M.le (denote M.toSeqData K ha) (denote M.toSeqData K hb))
    (ha' : HasType F Γ e' a A) (hb' : HasType F Γ η' b A) :
    M.le (denote M.toSeqData K ha') (denote M.toSeqData K hb') := by
  rw [H ha' ha, H hb' hb]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Native refinement closure preserves semantic validity once each primitive
rule has been proved. The hypotheses concern rules, not fields of model objects. -/
theorem validates_refines (O : ControlMonotone K) (H : WitnessCoherent M K)
    (eqSound : ∀ {n} {Γ : QCtx τ n} {a b : Term Φ n} {A} {e η : ε},
      EquationAxiom (ε := ε) F Γ a b A → ∀ (ha : HasType F Γ e a A) (hb : HasType F Γ η b A),
        denote M.toSeqData K ha = denote M.toSeqData K hb)
    (dirSound : ∀ {n} {Γ : QCtx τ n} {a b : Term Φ n} {A} {e η : ε} (p : Polarity),
      DirectionalAxiom (ε := ε) F p Γ a b A → ∀ (ha : HasType F Γ e a A) (hb : HasType F Γ η b A),
        p.orient M.le (denote M.toSeqData K ha) (denote M.toSeqData K hb))
    (uniformSound : ∀ {n m} {Γ : QCtx τ n} {Δ : QCtx τ m}
      {a b : Term Φ n} {c d : Term Φ m} {A B} (p : Polarity),
      UniformityRule (ε := ε) F p Γ a b A Δ c d B →
      ∀ (ha : HasType F Γ (⊤ : ε) a A) (hb : HasType F Γ (⊤ : ε) b A)
        (hc : HasType F Δ (⊤ : ε) c B) (hd : HasType F Δ (⊤ : ε) d B),
      p.orient M.le (denote M.toSeqData K ha) (denote M.toSeqData K hb) →
      p.orient M.le (denote M.toSeqData K hc) (denote M.toSeqData K hd))
    {R : Relation τ Φ} (hR : Validates M.toSeqData K R) :
    Validates M.toSeqData K (Refines (ε := ε) F R) := by
  intro n Γ a b A e η h
  induction h generalizing e η with
  | base h _ _ => exact hR h
  | refl _ =>
    intro ha hb
    rw [H ha hb]
    exact M.toSeqData.le_refl _
  | trans hab hbc ih ik =>
    intro ha hc
    obtain ⟨hb⟩ := hab.wellTyped.2
    let := M.toSeqData.homOrder
    exact le_trans (ih ha hb) (ik hb hc)
  | equation p h hfa hfb =>
    obtain ⟨da⟩ := hfa
    obtain ⟨db⟩ := hfb
    have he := eqSound h da db
    cases p <;> intro ha hb
    · apply le_of_coherent M K H da db _ ha hb
      rw [he]
      exact M.toSeqData.le_refl _
    · apply le_of_coherent M K H db da _ ha hb
      rw [he]
      exact M.toSeqData.le_refl _
  | directional p h hfa hfb =>
    obtain ⟨da⟩ := hfa
    obtain ⟨db⟩ := hfb
    have he := dirSound p h da db
    cases p <;> intro ha hb
    · exact le_of_coherent M K H da db he ha hb
    · exact le_of_coherent M K H db da he ha hb
  | uniformity p rule hfc hfd square ih =>
    obtain ⟨dc⟩ := hfc
    obtain ⟨dd⟩ := hfd
    cases p with
    | positive =>
      obtain ⟨⟨da⟩, ⟨db⟩⟩ := square.wellTyped
      intro hc hd
      exact le_of_coherent M K H dc dd (uniformSound .positive rule da db dc dd (ih da db)) hc hd
    | negative =>
      obtain ⟨⟨db⟩, ⟨da⟩⟩ := square.wellTyped
      intro hd hc
      exact le_of_coherent M K H dd dc (uniformSound .negative rule da db dc dd (ih db da)) hd hc
  | op h ih =>
    obtain ⟨⟨da⟩, ⟨db⟩⟩ := h.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.op le_top da) (.op le_top db)
      (M.compose_mono (ih da db) (M.toSeqData.le_refl _)) ha hb
  | let₁ s h k ih ik =>
    obtain ⟨⟨da⟩, ⟨da'⟩⟩ := h.wellTyped
    obtain ⟨⟨db⟩, ⟨db'⟩⟩ := k.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.let₁ s da db) (.let₁ s da' db')
      (M.compose_mono (M.toSeqData.le_refl _)
        (M.compose_mono (M.toSeqData.left_mono _ (ih da da')) (ik db db'))) ha hb
  | pair s h k ih ik =>
    obtain ⟨⟨da⟩, ⟨da'⟩⟩ := h.wellTyped
    obtain ⟨⟨db⟩, ⟨db'⟩⟩ := k.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.pair s da db) (.pair s da' db')
      (M.compose_mono (M.toSeqData.le_refl _) (M.toSeqData.tensor_mono (ih da da') (ik db db'))) ha hb
  | let₂ s h k ih ik =>
    obtain ⟨⟨da⟩, ⟨da'⟩⟩ := h.wellTyped
    obtain ⟨⟨db⟩, ⟨db'⟩⟩ := k.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.let₂ s da db) (.let₂ s da' db')
      (M.compose_mono (M.toSeqData.le_refl _)
        (M.compose_mono (M.toSeqData.left_mono _ (ih da da'))
          (M.compose_mono (M.toSeqData.le_refl _) (ik db db')))) ha hb
  | inl cap h ih =>
    obtain ⟨⟨da⟩, ⟨db⟩⟩ := h.wellTyped
    intro ha hb
    apply le_of_coherent M K H (.inl cap da) (.inl cap db) ?_ ha hb
    exact M.compose_mono (ih da db) (M.toSeqData.le_refl _)
  | inr cap h ih =>
    obtain ⟨⟨da⟩, ⟨db⟩⟩ := h.wellTyped
    intro ha hb
    apply le_of_coherent M K H (.inr cap da) (.inr cap db) ?_ ha hb
    exact M.compose_mono (ih da db) (M.toSeqData.le_refl _)
  | case cap s h l r ih il ir =>
    obtain ⟨⟨da⟩, ⟨da'⟩⟩ := h.wellTyped
    obtain ⟨⟨dl⟩, ⟨dl'⟩⟩ := l.wellTyped
    obtain ⟨⟨dr⟩, ⟨dr'⟩⟩ := r.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.case cap s da dl dr) (.case cap s da' dl' dr')
      (M.compose_mono (M.toSeqData.le_refl _)
        (M.compose_mono (M.toSeqData.left_mono _ (ih da da'))
          (M.compose_mono (M.toSeqData.le_refl _) (O.desc cap (il dl dl') (ir dr dr'))))) ha hb
  | abort cap h ih =>
    obtain ⟨⟨da⟩, ⟨db⟩⟩ := h.wellTyped
    intro ha hb
    apply le_of_coherent M K H (.abort cap da) (.abort cap db) ?_ ha hb
    exact M.compose_mono (ih da db) (M.toSeqData.le_refl _)
  | iter cap s hu h k ih ik =>
    obtain ⟨⟨da⟩, ⟨da'⟩⟩ := h.wellTyped
    obtain ⟨⟨db⟩, ⟨db'⟩⟩ := k.wellTyped
    intro ha hb
    exact le_of_coherent M K H (.iter cap s hu EffectSystem.iterable_top da db)
      (.iter cap s hu EffectSystem.iterable_top da' db')
      (M.compose_mono (M.toSeqData.le_refl _)
        (M.compose_mono (M.toSeqData.left_mono _ (ih da da'))
          (O.iterateWithContext cap _ _ _ (ik db db')))) ha hb

end Silmaril.Isotope.Refinement.Models.Denotation
