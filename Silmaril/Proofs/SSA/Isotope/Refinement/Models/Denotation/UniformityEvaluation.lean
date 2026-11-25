module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SequentialEquations
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.ControlWitnessCoherence

/-! # Interpreting the written directed uniformity square -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Denotation
open LetIter.LocallyNameless
universe u v w r
variable {α : Type u} [HasQuantity α]
variable {Φ : Type w} [HasTy Φ (Ty α)] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} (Ty α) Φ ε)

set_option backward.isDefEq.respectTransparency false in
/-- The left side of the written square retains the loop environment and runs the state map. -/
theorem denoteIter_uniformity_premise_left {n : Nat} {Γc Γl : QCtx (Ty α) n}
    {e η ξ : ε} {s b : Term Φ (n + 1)} {A C S : Ty α}
    (inner : Γc.Split Γl Γc)
    (hs : HasType .iter (Γc.snoc A) η s S)
    (hb : HasType .iter (Γl.snoc S) e b (coprod C S))
    (hk : HasType .iter (Γc.snoc A) ξ (.let₁ s b.underBinder) (coprod C S)) :
    denoteIter M hk = M.compose (M.right (split M.toSeqData inner) A)
      (M.compose (M.associator (packed Γl) (packed Γc) A)
        (M.compose (M.left (packed Γl) (denoteIter M hs)) (denoteIter M hb))) := by
  let hbu := hb.rename _ ((QCtx.Weakening.insertZero Γl A).up S)
  let sk := inner.snoc (.right (.used ⊤)) (A := A)
  let kl : HasType .iter (Γc.snoc A) (⊤ : ε) (.let₁ s b.underBinder) (coprod C S) :=
    .let₁ sk hs.top hbu.top
  rw [denoteIter_coherent M hk kl]
  have hs' : denoteIter M hs.top = denoteIter M hs := denoteIter_coherent M _ _
  have hb' : denoteIter M hbu.top = denoteIter M hb :=
    Sequential.denote_underBinder_zero M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
      (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) hb hbu.top
  change M.compose (split M.toSeqData sk)
    (M.compose (M.left (packed Γl) (denoteIter M hs.top)) (denoteIter M hbu.top)) = _
  rw [hs', hb', split_snoc_right]
  exact M.compose_assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The right side of the square retains the possibly linear comparison context
until selecting its exit or recurrence branch. -/
theorem denoteIter_uniformity_premise_right {n : Nat} {Γc Γl : QCtx (Ty α) n}
    {η ξ : ε} {s b' c : Term Φ (n + 1)} {A B C S : Ty α}
    (inner : Γc.Split Γl Γc)
    (hs : HasType .iter (Γc.snoc A) η s S)
    (hb' : HasType .iter (Γl.snoc A) (⊤ : ε) b' (coprod B A))
    (hc : HasType .iter (Γc.snoc B) (⊤ : ε) c C)
    (hk : HasType .iter (Γc.snoc A) ξ
      (.case b' (.inl c.underBinder) (.inr s.underBinder)) (coprod C S)) :
    denoteIter M hk = M.compose (M.right (split M.toSeqData inner.symm) A)
      (M.compose (M.associator (packed Γc) (packed Γl) A)
        (M.compose (M.left (packed Γc) (denoteIter M hb'))
          (M.compose (M.distribute (packed Γc) B A)
            (M.desc (M.compose (denoteIter M hc) (M.inl C S))
              (M.compose (denoteIter M hs) (M.inr C S)))))) := by
  let hcu := hc.rename _ ((QCtx.Weakening.insertZero Γc A).up B)
  let hsu := hs.rename _ ((QCtx.Weakening.insertZero Γc A).up A)
  let sk := inner.symm.snoc (.right (.used ⊤)) (A := A)
  let kr : HasType .iter (Γc.snoc A) (⊤ : ε)
      (.case b' (.inl c.underBinder) (.inr s.underBinder)) (coprod C S) :=
    .case trivial sk hb' (.inl trivial hcu) (.inr trivial hsu.top)
  rw [denoteIter_coherent M hk kr]
  have hc' : denoteIter M hcu = denoteIter M hc :=
    Sequential.denote_underBinder_zero M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
      (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) hc hcu
  have hs' : denoteIter M hsu.top = denoteIter M hs :=
    Sequential.denote_underBinder_zero M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
      (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) hs hsu.top
  change M.compose (split M.toSeqData sk)
    (M.compose (M.left (packed Γc) (denoteIter M hb'))
      (M.compose (M.distribute (packed Γc) B A)
        (M.desc (M.compose (denoteIter M hcu) (M.inl C S))
          (M.compose (denoteIter M hsu.top) (M.inr C S))))) = _
  rw [hc', hs', split_snoc_right]
  exact M.compose_assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The left conclusion first initializes, then maps the state before the loop. -/
theorem denoteIter_uniformity_conclusion_left {n : Nat} {Γ Γc Γl Γr : QCtx (Ty α) n}
    {e η ξ : ε} {a : Term Φ n} {s b : Term Φ (n + 1)} {A C S : Ty α}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γc) (hu : Γl.linearity = ⊤)
    (ha : HasType .iter Γr e a A) (hs : HasType .iter (Γc.snoc A) η s S)
    (hb : HasType .iter (Γl.snoc S) e b (coprod C S))
    (cD : Quantity.relevant ≤ quantity (packed Γl)) (dD : Quantity.affine ≤ quantity (packed Γl))
    (hk : HasType .iter Γ ξ (.let₁ a (.iter s b.underBinder)) C) :
    denoteIter M hk = M.compose (split M.toSeqData outer)
      (M.compose (M.left (packed Γc) (denoteIter M ha))
        (M.compose (M.right (split M.toSeqData inner) A)
          (M.compose (M.associator (packed Γl) (packed Γc) A)
            (M.compose (M.left (packed Γl) (denoteIter M hs))
              ((ControlData.iter M).iterateWithContext trivial (packed Γl) cD dD (denoteIter M hb)))))) := by
  let hbu := hb.rename _ ((QCtx.Weakening.insertZero Γl A).up S)
  let sk := inner.snoc (.right (.used ⊤)) (A := A)
  have hu0 : (Γl.snoc A .zero).linearity = ⊤ := by
    simp only [QCtx.linearity_snoc, Usage.linearity_zero, hu]
    rfl
  let ki : HasType .iter (Γc.snoc A) (⊤ : ε) (.iter s b.underBinder) C :=
    .iter trivial sk hu0 EffectSystem.iterable_top hs.top hbu.top
  let kl : HasType .iter Γ (⊤ : ε) (.let₁ a (.iter s b.underBinder)) C := .let₁ outer ha.top ki
  rw [denoteIter_coherent M hk kl]
  have hs' : denoteIter M hs.top = denoteIter M hs := denoteIter_coherent M _ _
  have ha' : denoteIter M ha.top = denoteIter M ha := denoteIter_coherent M _ _
  have hb' : denoteIter M hbu.top = denoteIter M hb :=
    Sequential.denote_underBinder_zero M.toSeqModel (ControlData.iter M) (ControlEnvironment.iter M)
      (Silmaril.Proofs.SSA.Isotope.Refinement.iterWitnessCoherent M) hb hbu.top
  change M.compose (split M.toSeqData outer)
    (M.compose (M.left (packed Γc) (denoteIter M ha.top))
      (M.compose (split M.toSeqData sk)
        (M.compose (M.left (packed Γl) (denoteIter M hs.top))
          ((ControlData.iter M).iterateWithContext trivial (packed Γl) cD dD (denoteIter M hbu.top))))) = _
  rw [ha', hs', hb', split_snoc_right, M.compose_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The right conclusion retains the comparison context while running the other loop. -/
theorem denoteIter_uniformity_conclusion_right {n : Nat} {Γ Γc Γl Γr : QCtx (Ty α) n}
    {e ξ : ε} {a : Term Φ n} {b' c : Term Φ (n + 1)} {A B C : Ty α}
    (outer : Γ.Split Γc Γr) (inner : Γc.Split Γl Γc) (hu : Γl.linearity = ⊤)
    (ha : HasType .iter Γr e a A)
    (hb' : HasType .iter (Γl.snoc A) (⊤ : ε) b' (coprod B A))
    (hc : HasType .iter (Γc.snoc B) (⊤ : ε) c C)
    (cD : Quantity.relevant ≤ quantity (packed Γl)) (dD : Quantity.affine ≤ quantity (packed Γl))
    (hk : HasType .iter Γ ξ (.let₁ (.iter a b') c) C) :
    denoteIter M hk = M.compose (split M.toSeqData outer)
      (M.compose (M.left (packed Γc) (denoteIter M ha))
        (M.compose (M.right (split M.toSeqData inner.symm) A)
          (M.compose (M.associator (packed Γc) (packed Γl) A)
            (M.compose (M.left (packed Γc)
              ((ControlData.iter M).iterateWithContext trivial (packed Γl) cD dD (denoteIter M hb')))
              (denoteIter M hc))))) := by
  obtain ⟨Γlr, sp, sq⟩ := outer.swapAssoc inner
  let ki : HasType .iter Γlr (⊤ : ε) (.iter a b') B :=
    .iter trivial sq hu EffectSystem.iterable_top ha.top hb'
  let kr : HasType .iter Γ (⊤ : ε) (.let₁ (.iter a b') c) C := .let₁ sp.symm ki hc
  rw [denoteIter_coherent M hk kr]
  have ha' : denoteIter M ha.top = denoteIter M ha := denoteIter_coherent M _ _
  let loop : M.Hom (product (packed Γl) A) B := (ControlData.iter M).iterateWithContext trivial (packed Γl) cD dD (denoteIter M hb')
  change M.compose (split M.toSeqData sp.symm)
    (M.compose (M.left (packed Γc)
      (M.compose (split M.toSeqData sq) (M.compose (M.left (packed Γl) (denoteIter M ha.top)) loop)))
      (denoteIter M hc)) = _
  rw [ha', M.left_compose]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (split M.toSeqData sp.symm) (M.left (packed Γc) (split M.toSeqData sq)), ← split_assoc M.toSeqData outer inner.symm sp.symm sq]
  simp only [M.left_compose, M.compose_assoc]
  rw [← M.compose_assoc (M.associator (packed Γc) (packed Γl) (packed Γr)),
    M.toSeqData.associator_natural_right]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.right (split M.toSeqData inner.symm) (packed Γr)),
    M.toSeqData.exchange_left_pure _ _ (split_pure _ _)]
  simp only [M.compose_assoc]
  rfl

end Silmaril.Isotope.Refinement.Models.Denotation
