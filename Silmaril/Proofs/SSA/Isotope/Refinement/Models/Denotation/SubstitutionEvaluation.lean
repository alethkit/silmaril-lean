module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionTensor

/-! # Evaluation order when substituting effectful computations -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.SeqData
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

theorem orient_compose (p : Polarity) {A B C : τ}
    {f f' : M.Hom A B} {g g' : M.Hom B C}
    (hf : p.orient M.le f f') (hg : p.orient M.le g g') :
    p.orient M.le (M.compose f g) (M.compose f' g') := by
  cases p <;> exact M.compose_mono hf hg

/-- The same mover inequality when its moving computation occupies the right wire. -/
theorem exchange_right_mover (p : Polarity) {e η : ε} {A B D E : τ}
    (f : M.Hom A B) (g : M.Hom D E) (hm : EffectSystem.moves p e η)
    (hf : M.hasEffect η f) (hg : M.hasEffect e g) :
    p.orient M.le (M.compose (M.left A g) (M.right f E))
      (M.compose (M.right f D) (M.left B g)) := by
  have hm' : EffectSystem.moves p.reverse η e := (EffectSystem.moves_reverse p η e).mpr hm
  have h := M.exchange p.reverse f g hm' hf hg
  cases p <;> exact h

/-- Move the right substitution component past the left body computation. -/
theorem tensor_comp_mover (p : Polarity) {e η : ε} {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (a : M.Hom B G) (b : M.Hom E H)
    (hm : EffectSystem.moves p e η) (hg : M.hasEffect e g) (ha : M.hasEffect η a) :
    p.orient M.le (M.compose (M.tensor f g) (M.tensor a b))
      (M.tensor (M.compose f a) (M.compose g b)) := by
  have h := M.orient_compose_left p
    (M.orient_compose_right p (M.exchange_right_mover p a g hm ha hg) (M.left G b))
    (M.right f D)
  simpa only [tensor, M.right_compose, M.left_compose, M.compose_assoc] using h

/-- Braiding reverses tensor positions while preserving computation order. -/
theorem tensor_braiding_order {A B D E : τ} (f : M.Hom A B) (g : M.Hom D E) :
    M.compose (M.tensor f g) (M.braiding B E) =
      M.compose (M.braiding A D) (M.compose (M.left D f) (M.right g B)) := by
  unfold tensor
  rw [M.compose_assoc, M.braiding_natural_right,
    ← M.compose_assoc, M.braiding_natural_left, M.compose_assoc]

/-- Continuation substitution moves past the initializer only after the
initializer's own substitution has executed. No self-commutation is required. -/
theorem tensor_bind_mover (p : Polarity) {e η : ε} {R S L D A B : τ}
    (f : M.Hom R S) (g : M.Hom L D) (a : M.Hom S A) (b : M.Hom (product D A) B)
    (hm : EffectSystem.moves p e η) (hg : M.hasEffect e g) (ha : M.hasEffect η a) :
    p.orient M.le
      (M.compose (M.tensor f g) (M.compose (M.braiding S D) (M.compose (M.left D a) b)))
      (M.compose (M.braiding R L)
        (M.compose (M.left L (M.compose f a)) (M.compose (M.right g A) b))) := by
  have h := M.orient_compose_left p
    (M.orient_compose_left p (M.orient_compose_right p (M.exchange p g a hm hg ha) b)
      (M.left L f)) (M.braiding R L)
  rw [← M.compose_assoc (M.tensor f g), M.tensor_braiding_order]
  simpa only [M.compose_assoc, M.left_compose] using h

end Silmaril.Isotope.Refinement.Models.SeqData
