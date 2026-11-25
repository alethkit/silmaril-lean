module

public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationSimulation
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionEvaluation

/-! # Directed effectful maps of persistent loop environments -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models
open CategoryTheory Denotation
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace SeqData
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem associator_natural_left {A B : τ} (f : M.Hom A B) (D E : τ) :
    M.compose (M.right (M.right f D) E) (M.associator B D E) =
      M.compose (M.associator A D E) (M.right f (product D E)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, right, associator, Category.assoc,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.eqToHom_whiskerRight,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← PremonoidalCategory.whiskerRight_eqToHom_assoc f (M.tensor_obj D E)]
  simp [PremonoidalCategory.associator_naturality_left_assoc]

theorem associator_natural_middle (D : τ) {A B : τ} (f : M.Hom A B) (E : τ) :
    M.compose (M.right (M.left D f) E) (M.associator D B E) =
      M.compose (M.associator D A E) (M.left D (M.right f E)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [compose, right, left, associator, Category.assoc,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.eqToHom_whiskerRight,
    PremonoidalCategory.whiskerLeft_comp, PremonoidalCategory.whiskerLeft_eqToHom,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  simp [PremonoidalCategory.associator_naturality_middle_assoc]

/-- A directed diagonal comparison also permits the reverse evaluation order,
by cocommutativity of the two diagonals. No self-mover is required. -/
theorem copy_reverse (p : Polarity) {D E : τ} (f : M.Hom D E)
    (cD : Quantity.relevant ≤ quantity D) (cE : Quantity.relevant ≤ quantity E)
    (hc : p.orient M.le (M.compose f (M.copy E cE)) (M.compose (M.copy D cD) (M.tensor f f))) :
    p.orient M.le (M.compose f (M.copy E cE))
      (M.compose (M.copy D cD) (M.compose (M.left D f) (M.right f E))) := by
  have h := M.orient_compose_right p hc (M.braiding E E)
  simp only [M.compose_assoc] at h
  rw [M.copy_braiding, M.tensor_braiding_order, ← M.compose_assoc (M.copy D cD), M.copy_braiding] at h
  exact h

/-- Copy the body environment before computing the retained environment. -/
theorem copy_context_directed (p : Polarity) {D E : τ} (f : M.Hom D E)
    (cD : Quantity.relevant ≤ quantity D) (cE : Quantity.relevant ≤ quantity E) (A : τ)
    (hc : p.orient M.le (M.compose f (M.copy E cE)) (M.compose (M.copy D cD) (M.tensor f f))) :
    p.orient M.le
      (M.compose (M.right f A) (M.compose (M.right (M.copy E cE) A) (M.associator E E A)))
      (M.compose (M.compose (M.right (M.copy D cD) A) (M.associator D D A))
        (M.compose (M.left D (M.right f A)) (M.right f (product E A)))) := by
  have h := M.orient_compose_right p (M.orient_right p (M.copy_reverse p f cD cE hc) A)
    (M.associator E E A)
  simp only [M.right_compose, M.compose_assoc] at h
  rw [M.associator_natural_left,
    ← M.compose_assoc (M.right (M.left D f) A), M.associator_natural_middle] at h
  simpa only [M.compose_assoc] using h

end SeqData
namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- Resource-compatible effectful environment maps induce a directed simulation
of one loop step. The mover only crosses the original body's effect. -/
theorem contextStep_directed_environment (p : Polarity) {e η : ε} {D E A B : τ}
    (f : M.Hom D E) (body : M.Hom (product E A) (coprod B A))
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (hf : M.hasEffect e f) (hb : M.hasEffect η body) (hm : EffectSystem.moves p e η)
    (hc : p.orient M.le (M.compose f (M.copy E cE)) (M.compose (M.copy D cD) (M.tensor f f)))
    (hd : p.orient M.le (M.compose f (M.discard E dE)) (M.discard D dD)) :
    p.orient M.le
      (M.compose (M.right f A) ((ControlData.iter M).contextStep trivial E cE dE body))
      (M.compose ((ControlData.iter M).contextStep trivial D cD dD (M.compose (M.right f A) body))
        (M.desc (M.inl B (product E A)) (M.compose (M.right f A) (M.inr B (product E A))))) := by
  let exitD := M.compose (M.right (M.discard D dD) B) (M.leftUnitor B)
  let exitE := M.compose (M.right (M.discard E dE) B) (M.leftUnitor B)
  let tailD := M.compose (M.distribute D B A)
    (M.desc (M.compose exitD (M.inl B (product D A))) (M.inr B (product D A)))
  let tailE := M.compose (M.distribute E B A)
    (M.desc (M.compose exitE (M.inl B (product E A))) (M.inr B (product E A)))
  let transfer := M.desc (M.inl B (product E A)) (M.compose (M.right f A) (M.inr B (product E A)))
  have hdel : p.orient M.le (M.compose (M.right f B) exitE) exitD := by
    have h := M.toSeqData.orient_compose_right p (M.toSeqData.orient_right p hd B) (M.leftUnitor B)
    simpa only [exitD, exitE, M.right_compose, M.compose_assoc] using h
  have ht : p.orient M.le (M.compose (M.right f (coprod B A)) tailE) (M.compose tailD transfer) := by
    have h1 := M.toSeqData.orient_compose_right p hdel (M.inl B (product E A))
    have h2 : p.orient M.le (M.compose (M.right f A) (M.inr B (product E A)))
        (M.compose (M.right f A) (M.inr B (product E A))) := by
      cases p <;> exact M.toSeqData.le_refl _
    have h3 : p.orient M.le
        (M.desc (M.compose (M.compose (M.right f B) exitE) (M.inl B (product E A)))
          (M.compose (M.right f A) (M.inr B (product E A))))
        (M.desc (M.compose exitD (M.inl B (product E A)))
          (M.compose (M.right f A) (M.inr B (product E A)))) := by
      cases p <;> exact M.toCaseData.desc_mono h1 h2
    have h4 := M.toSeqData.orient_compose_left p h3 (M.distribute D B A)
    dsimp [tailD, tailE, transfer]
    rw [← M.compose_assoc, M.toCaseData.distribute_natural]
    simpa only [M.compose_assoc, M.toCaseData.desc_compose, M.toCaseData.inl_desc,
      M.toCaseData.inr_desc] using h4
  let cpD := M.compose (M.right (M.copy D cD) A) (M.associator D D A)
  let cpE := M.compose (M.right (M.copy E cE) A) (M.associator E E A)
  have h1 := M.toSeqData.orient_compose_right p
    (M.toSeqData.copy_context_directed p f cD cE A hc) (M.compose (M.left E body) tailE)
  have h2 := M.toSeqData.orient_compose_left p
    (M.toSeqData.orient_compose_left p
      (M.toSeqData.orient_compose_right p (M.toSeqData.exchange p f body hm hf hb) tailE)
      (M.left D (M.right f A))) cpD
  have h3 := M.toSeqData.orient_compose_left p ht
    (M.compose cpD (M.left D (M.compose (M.right f A) body)))
  have hall := M.toSeqData.orient_trans p
    (by simpa only [cpD, cpE, M.compose_assoc] using h1)
    (M.toSeqData.orient_trans p (by simpa only [cpD, M.compose_assoc] using h2)
      (by simpa only [cpD, M.left_compose, M.compose_assoc] using h3))
  simpa only [ControlData.contextStep, ControlData.iter, ControlData.ofCase,
    cpD, cpE, tailD, tailE, transfer, exitD, exitE, M.left_compose, M.compose_assoc] using hall

/-- Directed uniformity transports a resource-compatible environment map
through an entire loop, allowing the transformed body to have arbitrary effect. -/
theorem iterateWithContext_directed_environment (p : Polarity) {e η : ε} {D E A B : τ}
    (f : M.Hom D E) (body : M.Hom (product E A) (coprod B A))
    (body' : M.Hom (product D A) (coprod B A))
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (cE : Quantity.relevant ≤ quantity E) (dE : Quantity.affine ≤ quantity E)
    (hi : EffectSystem.iterable η) (hf : M.hasEffect e f) (hb : M.hasEffect η body)
    (hm : EffectSystem.moves p e η)
    (hc : p.orient M.le (M.compose f (M.copy E cE)) (M.compose (M.copy D cD) (M.tensor f f)))
    (hd : p.orient M.le (M.compose f (M.discard E dE)) (M.discard D dD))
    (hs : p.orient M.le (M.compose (M.right f A) body) body') :
    p.orient M.le
      (M.compose (M.right f A) ((ControlData.iter M).iterateWithContext trivial E cE dE body))
      ((ControlData.iter M).iterateWithContext trivial D cD dD body') := by
  have hstep : M.hasEffect η ((ControlData.iter M).contextStep trivial E cE dE body) := by
    apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.copy_pure E cE)))
    apply M.compose_effect (M.effect_mono bot_le (M.associator_pure _ _ _))
    apply M.compose_effect (M.left_effect _ hb)
    apply M.compose_effect (M.effect_mono bot_le (M.toCaseData.distribute_pure _ _ _))
    apply M.toCaseData.desc_effect
    · apply M.compose_effect (M.effect_mono bot_le (M.right_effect _ (M.discard_pure E dE)))
      exact M.compose_effect (M.effect_mono bot_le (M.leftUnitor_pure _))
        (M.effect_mono bot_le (M.toCaseData.inl_pure _ _))
    · exact M.effect_mono bot_le (M.toCaseData.inr_pure _ _)
  apply M.uniformity p hi hm (M.right_effect A hf) hstep
  have hcstep : p.orient M.le
      ((ControlData.iter M).contextStep trivial D cD dD (M.compose (M.right f A) body))
      ((ControlData.iter M).contextStep trivial D cD dD body') := by
    cases p <;> exact ControlMonotone.contextStep (K := ControlData.iter M) trivial D cD dD hs
  exact M.toSeqData.orient_trans p
    (M.contextStep_directed_environment p f body cD dD cE dE hf hb hm hc hd)
    (M.toSeqData.orient_compose_right p hcstep
      (M.desc (M.inl B (product E A)) (M.compose (M.right f A) (M.inr B (product E A)))))

end IterModel
end Silmaril.Isotope.Refinement.Models
