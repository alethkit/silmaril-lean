module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.UniformityCoaction

/-! # Lifting a written uniformity square to categorical iteration -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Isotope.Refinement.Models
open Denotation
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]

namespace CaseData
variable (M : CaseData.{u,v,w,r} τ Φ ε)

/-- A pure coaction distributes independently through either sum branch. -/
theorem contextAction_distribute {C D A B : τ} (i : M.Hom C (product D C))
    (hi : M.hasEffect ⊥ i) :
    M.compose (M.toSeqData.contextAction i (coprod B A))
      (M.compose (M.left D (M.distribute C B A)) (M.distribute D (product C B) (product C A))) =
      M.compose (M.distribute C B A)
        (M.desc (M.compose (M.toSeqData.contextAction i B) (M.inl (product D (product C B)) (product D (product C A))))
          (M.compose (M.toSeqData.contextAction i A) (M.inr (product D (product C B)) (product D (product C A))))) := by
  apply M.distributed_hom_ext
  · rw [← M.compose_assoc, ← M.toSeqData.contextAction_natural i hi]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left D (M.left C (M.inl B A))), ← M.left_compose,
      M.left_inl_distribute, M.left_inl_distribute, ← M.compose_assoc,
      M.left_inl_distribute, M.inl_desc]
  · rw [← M.compose_assoc, ← M.toSeqData.contextAction_natural i hi]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left D (M.left C (M.inr B A))), ← M.left_compose,
      M.left_inr_distribute, M.left_inr_distribute, ← M.compose_assoc,
      M.left_inr_distribute, M.inr_desc]

/-- The machine retaining the comparison context preserves its left coaction. -/
theorem contextAction_retainedStep {C D A B : τ}
    (i : M.Hom C (product D C)) (j : M.Hom C (product C D))
    (hi : M.hasEffect ⊥ i) (hj : M.hasEffect ⊥ j)
    (hm : M.compose j (M.compose (M.right i D) (M.associator D C D)) = M.compose i (M.left D j))
    (b : M.Hom (product D A) (coprod B A)) :
    M.compose (M.toSeqData.contextAction i A)
      (M.compose (M.left D (M.compose (M.toSeqData.contextAction j A)
        (M.compose (M.left C b) (M.distribute C B A))))
        (M.distribute D (product C B) (product C A))) =
    M.compose (M.compose (M.toSeqData.contextAction j A) (M.compose (M.left C b) (M.distribute C B A)))
      (M.desc (M.compose (M.toSeqData.contextAction i B) (M.inl (product D (product C B)) (product D (product C A))))
        (M.compose (M.toSeqData.contextAction i A) (M.inr (product D (product C B)) (product D (product C A))))) := by
  simp only [M.left_compose, M.compose_assoc]
  rw [← M.compose_assoc (M.toSeqData.contextAction i A), M.toSeqData.contextAction_mixed i j hi hj hm]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.toSeqData.contextAction i (product D A)), M.toSeqData.contextAction_natural i hi b]
  simp only [M.compose_assoc]
  rw [M.contextAction_distribute i hi]

end CaseData
namespace IterModel
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- A state comparison using a supplied environment preserves the copy prefix. -/
theorem contextAction_state_copy {C D A S : τ} (i : M.Hom C (product D C))
    (hi : M.hasEffect ⊥ i) (cD : Quantity.relevant ≤ quantity D)
    (hco : M.compose i (M.compose (M.right (M.copy D cD) C) (M.associator D D C)) = M.compose i (M.left D i))
    (s : M.Hom (product C A) S) :
    M.compose (M.compose (M.toSeqData.contextAction i A) (M.left D s))
      (M.compose (M.right (M.copy D cD) S) (M.associator D D S)) =
      M.compose (M.toSeqData.contextAction i A)
        (M.left D (M.compose (M.toSeqData.contextAction i A) (M.left D s))) := by
  rw [M.compose_assoc, M.copy_state_natural cD s,
    ← M.compose_assoc, ← M.toSeqData.contextAction_duplicate i hi cD hco A]
  simp only [M.left_compose, M.compose_assoc]

/-- The supplied environment disappears on an arbitrary exit continuation. -/
theorem contextAction_exit {C D A B : τ} (i : M.Hom C (product D C))
    (hi : M.hasEffect ⊥ i) (dD : Quantity.affine ≤ quantity D)
    (hco : M.compose i (M.compose (M.right (M.discard D dD) C) (M.leftUnitor C)) = M.identity C)
    (c : M.Hom (product C A) B) :
    M.compose (M.toSeqData.contextAction i A)
      (M.compose (M.left D c) (M.compose (M.right (M.discard D dD) B) (M.leftUnitor B))) = c := by
  rw [M.exit_natural dD c, ← M.compose_assoc, M.toSeqData.contextAction_counit i hi dD hco A,
    M.identity_compose]

/-- A comparison in the written premise lifts to the state-retaining machines.
Only the supplied component is copied or discarded. -/
theorem contextAction_uniformity_square (p : Polarity) {C D A B X S : τ}
    (i : M.Hom C (product D C)) (j : M.Hom C (product C D))
    (hi : M.hasEffect ⊥ i) (hj : M.hasEffect ⊥ j)
    (cD : Quantity.relevant ≤ quantity D) (dD : Quantity.affine ≤ quantity D)
    (hco : M.compose i (M.compose (M.right (M.copy D cD) C) (M.associator D D C)) = M.compose i (M.left D i))
    (hmix : M.compose j (M.compose (M.right i D) (M.associator D C D)) = M.compose i (M.left D j))
    (hunit : M.compose i (M.compose (M.right (M.discard D dD) C) (M.leftUnitor C)) = M.identity C)
    (s : M.Hom (product C A) S) (b : M.Hom (product D S) (coprod X S))
    (b' : M.Hom (product D A) (coprod B A)) (c : M.Hom (product C B) X)
    (hs : p.orient M.le
      (M.compose (M.compose (M.toSeqData.contextAction i A) (M.left D s)) b)
      (M.compose (M.compose (M.toSeqData.contextAction j A) (M.compose (M.left C b') (M.distribute C B A)))
        (M.desc (M.compose c (M.inl X S)) (M.compose s (M.inr X S))))) :
    p.orient M.le
      (M.compose (M.compose (M.toSeqData.contextAction i A) (M.left D s))
        ((ControlData.iter M).contextStep trivial D cD dD b))
      (M.compose (M.compose (M.toSeqData.contextAction j A) (M.compose (M.left C b') (M.distribute C B A)))
        (M.desc (M.compose c (M.inl X (product D S)))
          (M.compose (M.compose (M.toSeqData.contextAction i A) (M.left D s)) (M.inr X (product D S))))) := by
  let h := M.compose (M.toSeqData.contextAction i A) (M.left D s)
  let g := M.compose (M.toSeqData.contextAction j A) (M.compose (M.left C b') (M.distribute C B A))
  let ex := M.compose (M.right (M.discard D dD) X) (M.leftUnitor X)
  let tail := M.compose (M.distribute D X S)
    (M.desc (M.compose ex (M.inl X (product D S))) (M.inr X (product D S)))
  have hlift := M.toSeqData.orient_compose_left p
    (M.toSeqData.orient_compose_right p (M.toSeqData.orient_left p D hs) tail)
    (M.toSeqData.contextAction i A)
  have hleft : M.compose (M.toSeqData.contextAction i A) (M.compose (M.left D (M.compose h b)) tail) =
      M.compose h ((ControlData.iter M).contextStep trivial D cD dD b) := by
    rw [M.left_compose]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.toSeqData.contextAction i A) (M.left D h),
      ← M.contextAction_state_copy i hi cD hco s]
    simp only [h, tail, ex, ControlData.contextStep, ControlData.iter, ControlData.ofCase,
      M.compose_assoc]
  have hright : M.compose (M.toSeqData.contextAction i A)
      (M.compose (M.left D (M.compose g (M.desc (M.compose c (M.inl X S)) (M.compose s (M.inr X S)))) ) tail) =
      M.compose g (M.desc (M.compose c (M.inl X (product D S))) (M.compose h (M.inr X (product D S)))) := by
    dsimp [tail]
    simp only [M.left_compose, M.compose_assoc]
    rw [← M.compose_assoc (M.left D (M.desc _ _)) (M.distribute D X S), M.toCaseData.distribute_map]
    simp only [M.compose_assoc]
    rw [← M.compose_assoc (M.left D g) (M.distribute D (product C B) (product C A)),
      ← M.compose_assoc (M.toSeqData.contextAction i A),
      M.toCaseData.contextAction_retainedStep i j hi hj hmix b']
    simp only [M.compose_assoc, M.toCaseData.desc_compose, M.toCaseData.inl_desc, M.toCaseData.inr_desc]
    rw [← M.compose_assoc (M.toSeqData.contextAction i B) (M.left D c),
      ← M.compose_assoc (M.compose (M.toSeqData.contextAction i B) (M.left D c)) ex]
    have he : M.compose (M.compose (M.toSeqData.contextAction i B) (M.left D c)) ex = c := by
      simpa only [ex, M.compose_assoc] using M.contextAction_exit i hi dD hunit c
    rw [he]
    simp only [h, g, M.compose_assoc]
  change p.orient M.le (M.compose h ((ControlData.iter M).contextStep trivial D cD dD b)) _
  exact (congrArg₂ (fun f g => p.orient M.le f g) hleft hright).mp hlift

end IterModel
end Silmaril.Isotope.Refinement.Models
