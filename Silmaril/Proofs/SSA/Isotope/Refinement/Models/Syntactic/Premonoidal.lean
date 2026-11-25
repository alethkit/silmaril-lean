module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Triangle
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.AssociatorInverses

/-! # The syntactic premonoidal structure

The tensor data, separate functoriality, structural naturality, centrality and
triangle are derived from native syntax. The assembly constructor takes the
remaining pentagon proof explicitly, so global coherence can be proved in a
later module without a cyclic dependency or an added syntactic axiom.
-/

@[expose] public section
noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open CategoryTheory
open scoped MonoidalCategory PremonoidalCategory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} (hR : R.RenamingClosed)

/-- Product syntax, sequential tensor, and the actual structural isomorphisms. -/
instance monoidalStruct : MonoidalCategoryStruct (Object ε F R hR) where
  tensorObj A B := ⟨product A.type B.type⟩
  whiskerLeft A _ _ f := left hR A.type f
  whiskerRight f B := right hR f B.type
  tensorUnit := ⟨Silmaril.unit⟩
  associator A B C :=
    { hom := assoc A.type B.type C.type
      inv := assocInv A.type B.type C.type
      hom_inv_id := assoc_assocInv hR A.type B.type C.type
      inv_hom_id := assocInv_assoc hR A.type B.type C.type }
  leftUnitor A :=
    { hom := leftUnit A.type
      inv := leftUnitInv A.type
      hom_inv_id := leftUnit_leftUnitInv hR A.type
      inv_hom_id := leftUnitInv_leftUnit hR A.type }
  rightUnitor A :=
    { hom := rightUnit A.type
      inv := rightUnitInv A.type
      hom_inv_id := rightUnit_rightUnitInv hR A.type
      inv_hom_id := rightUnitInv_rightUnit hR A.type }

/-- Purity implies centrality for the actual syntactic tensor operations. -/
theorem pure_isCentral {A B : Object ε F R hR} {f : A ⟶ B}
    (hf : hasEffect (⊥ : ε) f) : PremonoidalCategory.IsCentral f :=
  ⟨fun g => pure_exchange_left hR hf g, fun g => pure_exchange_right hR g hf⟩

/-- Assemble the native premonoidal category from its independently proved
pentagon. Every other field is already a theorem of quantitative refinement. -/
@[instance_reducible] def premonoidalOfPentagon
    (pentagon : ∀ A B C D : Object ε F R hR, MonoidalCategory.Pentagon A B C D) :
    PremonoidalCategory (Object ε F R hR) where
  __ := monoidalStruct hR
  tensorHom_def _ _ := rfl
  whiskerLeft_id A B := left_identity hR A.type B.type
  whiskerLeft_comp A _ _ _ f g := left_compose hR A.type f g
  id_whiskerRight A B := identity_right hR A.type B.type
  comp_whiskerRight f g D := compose_right hR f g D.type
  associator_central A B C := pure_isCentral hR (assoc_pure A.type B.type C.type)
  leftUnitor_central A := pure_isCentral hR (leftUnit_pure A.type)
  rightUnitor_central A := pure_isCentral hR (rightUnit_pure A.type)
  associator_naturality_left f B C := assoc_natural_left hR f B.type C.type
  associator_naturality_middle A _ _ f D := assoc_natural_middle hR A.type f D.type
  associator_naturality_right A B _ _ f := assoc_natural_right hR A.type B.type f
  leftUnitor_naturality f := leftUnit_natural hR f
  rightUnitor_naturality f := rightUnit_natural hR f
  pentagon := pentagon
  triangle A B := triangle hR A.type B.type

/-- The same tensor data on the literal type universe, for the fixed-type
categorical model interface. The wrapper category remains available in parallel. -/
@[instance_reducible] def typeMonoidalStruct :
    letI := category (ε := ε) F R hR
    MonoidalCategoryStruct τ := by
  letI := category (ε := ε) F R hR
  exact
    { tensorObj := product
      whiskerLeft := fun A _ _ f => left hR A f
      whiskerRight := fun f B => right hR f B
      tensorUnit := Silmaril.unit
      associator := assocIso hR
      leftUnitor := leftUnitIso hR
      rightUnitor := rightUnitIso hR }

/-- Assemble the corresponding premonoidal structure on the literal types.
Its pentagon premise is exactly the wrapper category's premise. -/
@[instance_reducible] def typePremonoidalOfPentagon
    (pentagon : ∀ A B C D : Object ε F R hR, MonoidalCategory.Pentagon A B C D) :
    letI := category (ε := ε) F R hR
    PremonoidalCategory τ := by
  letI := category (ε := ε) F R hR
  let M := premonoidalOfPentagon hR pentagon
  exact
    { typeMonoidalStruct hR with
      tensorHom_def := fun _ _ => rfl
      whiskerLeft_id := fun A B => M.whiskerLeft_id ⟨A⟩ ⟨B⟩
      whiskerLeft_comp := fun A _ _ _ f g => M.whiskerLeft_comp ⟨A⟩ f g
      id_whiskerRight := fun A B => M.id_whiskerRight ⟨A⟩ ⟨B⟩
      comp_whiskerRight := fun f g D => M.comp_whiskerRight f g ⟨D⟩
      associator_central := by
        intro A B C
        constructor
        · intro D E g
          exact pure_exchange_left hR (assoc_pure A B C) g
        · intro D E g
          exact pure_exchange_right hR g (assoc_pure A B C)
      leftUnitor_central := by
        intro A
        constructor
        · intro D E g
          exact pure_exchange_left hR (leftUnit_pure A) g
        · intro D E g
          exact pure_exchange_right hR g (leftUnit_pure A)
      rightUnitor_central := by
        intro A
        constructor
        · intro D E g
          exact pure_exchange_left hR (rightUnit_pure A) g
        · intro D E g
          exact pure_exchange_right hR g (rightUnit_pure A)
      associator_naturality_left := fun f B C => M.associator_naturality_left f ⟨B⟩ ⟨C⟩
      associator_naturality_middle := fun A _ _ f D => M.associator_naturality_middle ⟨A⟩ f ⟨D⟩
      associator_naturality_right := fun A B _ _ f => M.associator_naturality_right ⟨A⟩ ⟨B⟩ f
      leftUnitor_naturality := fun f => M.leftUnitor_naturality f
      rightUnitor_naturality := fun f => M.rightUnitor_naturality f
      pentagon := fun A B C D => M.pentagon ⟨A⟩ ⟨B⟩ ⟨C⟩ ⟨D⟩
      triangle := fun A B => M.triangle ⟨A⟩ ⟨B⟩ }

end Silmaril.Isotope.Refinement.Models.Syntactic
