module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Denotation.SubstitutionNaturality

/-! # Ordered tensor calculus for substitution -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Refinement.Models.SeqData

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : SeqData.{u,v,w,r} τ Φ ε)

/-- Reassociating a tensor preserves its left-to-right computation order. -/
theorem tensor_associator {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom G H) :
    M.compose (M.tensor (M.tensor f g) h) (M.associator B E H) =
      M.compose (M.associator A D G) (M.tensor f (M.tensor g h)) := by
  let := M.category
  let := M.homOrder
  let := M.premonoidal
  let := M.symmetric
  simp only [tensor, compose, right, left, associator,
    PremonoidalCategory.comp_whiskerRight, PremonoidalCategory.whiskerLeft_comp,
    PremonoidalCategory.eqToHom_whiskerRight, PremonoidalCategory.whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← PremonoidalCategory.transport_whiskerLeft_assoc (M.tensor_obj B E).symm h]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [PremonoidalCategory.associator_naturality_right_assoc]
  rw [PremonoidalCategory.whiskerRight_eqToHom_assoc f (M.tensor_obj D G).symm]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [PremonoidalCategory.associator_naturality_middle_assoc,
    PremonoidalCategory.associator_naturality_left_assoc]
  simp only [eqToHom_trans]

/-- A tensor can be braided past commuting computations. -/
theorem tensor_braiding_commutes {e η : ε} {A B D E : τ}
    (f : M.Hom A B) (g : M.Hom D E) (hm : EffectSystem.commutes e η)
    (hf : M.hasEffect e f) (hg : M.hasEffect η g) :
    M.compose (M.tensor f g) (M.braiding B E) =
      M.compose (M.braiding A D) (M.tensor g f) := by
  unfold tensor
  rw [M.compose_assoc, M.braiding_natural_right]
  rw [← M.compose_assoc, M.braiding_natural_left, M.compose_assoc]
  rw [← M.exchange_commutes g f hm.symm hg hf]

/-- The right-output slot of a split passes through a substitution tensor. -/
theorem tensor_split_right {A B C D X Y : τ}
    (f : M.Hom A B) (g : M.Hom C D) (s : M.Hom B (product X Y))
    (hs : M.hasEffect ⊥ s) :
    M.compose (M.tensor f g)
      (M.compose (M.right s D) (M.associator X Y D)) =
      M.compose (M.tensor (M.compose f s) g) (M.associator X Y D) := by
  unfold tensor
  rw [M.right_compose]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.left B g) (M.right s D), ← M.exchange_left_pure s g hs]
  simp only [M.compose_assoc]

/-- Inverse reassociation also preserves evaluation order. -/
theorem tensor_associatorInv {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom G H) :
    M.compose (M.tensor f (M.tensor g h)) (M.associatorInv B E H) =
      M.compose (M.associatorInv A D G) (M.tensor (M.tensor f g) h) := by
  have he := congrArg (fun k => M.compose (M.associatorInv A D G)
    (M.compose k (M.associatorInv B E H))) (M.tensor_associator f g h)
  simp only [← M.compose_assoc, M.associator_inv_hom, M.identity_compose] at he
  simpa only [M.compose_assoc, M.associator_hom_inv, M.compose_identity] using he.symm

theorem tensor_left_after {A B D E G : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom E G) :
    M.compose (M.tensor f g) (M.left B h) = M.tensor f (M.compose g h) := by
  simp only [tensor, M.left_compose, M.compose_assoc]

theorem tensor_right_after {A B D E G : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom B G) (hh : M.hasEffect ⊥ h) :
    M.compose (M.tensor f g) (M.right h E) = M.tensor (M.compose f h) g := by
  unfold tensor
  rw [M.right_compose]
  simp only [M.compose_assoc]
  rw [← M.exchange_left_pure h g hh]

theorem tensor_left_before {A B D E G : τ}
    (f : M.Hom A B) (s : M.Hom D E) (g : M.Hom E G) (hs : M.hasEffect ⊥ s) :
    M.compose (M.left A s) (M.tensor f g) = M.tensor f (M.compose s g) := by
  unfold tensor
  rw [M.left_compose, ← M.compose_assoc, ← M.exchange_right_pure f s hs]
  simp only [M.compose_assoc]

theorem tensor_right_before {A B D E G : τ}
    (s : M.Hom A B) (f : M.Hom B G) (g : M.Hom D E) :
    M.compose (M.right s D) (M.tensor f g) = M.tensor (M.compose s f) g := by
  simp only [tensor, M.right_compose, M.compose_assoc]

/-- Middle interchange requires exactly the effects crossing in the middle. -/
theorem tensor_middleSwap {e η : ε} {A B D E G H I J : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom G H) (k : M.Hom I J)
    (hm : EffectSystem.commutes e η) (hg : M.hasEffect e g) (hh : M.hasEffect η h) :
    M.compose (M.tensor (M.tensor f g) (M.tensor h k)) (M.middleSwap B E H J) =
      M.compose (M.middleSwap A D G I) (M.tensor (M.tensor f h) (M.tensor g k)) := by
  unfold middleSwap
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor (M.tensor f g) (M.tensor h k)), M.tensor_associator]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor f (M.tensor g (M.tensor h k))),
    M.tensor_left_after, M.tensor_associatorInv,
    ← M.tensor_left_before f _ _ (M.associatorInv_pure D G I)]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor f (M.tensor (M.tensor g h) k)),
    M.tensor_left_after, M.tensor_right_after _ _ _ (M.braiding_pure E H),
    M.tensor_braiding_commutes g h hm hg hh,
    ← M.tensor_right_before, ← M.tensor_left_before f _ _
      (M.right_effect _ (M.braiding_pure D G))]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor f (M.tensor (M.tensor h g) k)),
    M.tensor_left_after, M.tensor_associator,
    ← M.tensor_left_before f _ _ (M.associator_pure G D I)]
  simp only [M.compose_assoc]
  rw [M.tensor_associatorInv]

/-- Moving a final component left exchanges just that component and its neighbor. -/
theorem tensor_moveLeft {e η : ε} {A B D E G H : τ}
    (f : M.Hom A B) (g : M.Hom D E) (h : M.Hom G H)
    (hm : EffectSystem.commutes e η) (hg : M.hasEffect e g) (hh : M.hasEffect η h) :
    M.compose (M.tensor (M.tensor f g) h)
      (M.compose (M.associator B E H)
        (M.compose (M.left B (M.braiding E H)) (M.associatorInv B H E))) =
      M.compose (M.associator A D G)
        (M.compose (M.left A (M.braiding D G))
          (M.compose (M.associatorInv A G D) (M.tensor (M.tensor f h) g))) := by
  rw [← M.compose_assoc (M.tensor (M.tensor f g) h), M.tensor_associator]
  simp only [M.compose_assoc]
  rw [← M.compose_assoc (M.tensor f (M.tensor g h)), M.tensor_left_after,
    M.tensor_braiding_commutes g h hm hg hh,
    ← M.tensor_left_before f _ _ (M.braiding_pure D G)]
  simp only [M.compose_assoc]
  rw [M.tensor_associatorInv]

end Silmaril.Isotope.Refinement.Models.SeqData
