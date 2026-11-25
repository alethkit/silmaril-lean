module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Premonoidal
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Pentagon
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Hexagons

/-! # The native ordered symmetric premonoidal category

All coherence fields are theorems of quantitative refinement, including the
pentagon and both hexagons. Effect membership and directed exchange are
inherited from typing and the written mover relation.
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

instance premonoidal : PremonoidalCategory (Object ε F R hR) :=
  premonoidalOfPentagon hR (fun A B C D => pentagon hR A.type B.type C.type D.type)

instance symmetric : SymmetricPremonoidalCategory (Object ε F R hR) where
  braiding A B :=
    { hom := swap A.type B.type
      inv := swap B.type A.type
      hom_inv_id := swap_swap hR A.type B.type
      inv_hom_id := swap_swap hR B.type A.type }
  naturality_left f C := swap_right_natural hR f C.type
  naturality_right A _ _ f := swap_left_natural hR A.type f
  hexagon_forward A B C := hexagon_forward hR A.type B.type C.type
  hexagon_reverse A B C := hexagon_reverse hR A.type B.type C.type
  braiding_central A B := pure_isCentral hR (swap_pure A.type B.type)
  symmetry A B := swap_swap hR A.type B.type

instance orderedPremonoidal : OrderedPremonoidal (Object ε F R hR) where
  comp_mono := compose_mono hR
  whiskerLeft_mono A := left_mono hR A.type
  whiskerRight_mono B := right_mono hR B.type

/-- The actual effectful structure of the native syntactic category. -/
def effects : EffectfulCategory (Object ε F R hR) ε where
  effect e := fun _ _ f => hasEffect e f
  mono h _ _ _ hf := hasEffect_mono h hf
  top := hasEffect_top
  id _ A := hasEffect_mono bot_le (identity_pure A.type)
  comp := compose_effect hR
  whiskerLeft A := left_effect hR A.type
  whiskerRight B := right_effect hR B.type
  associator A B C := assoc_pure A.type B.type C.type
  associator_inv A B C := assocInv_pure A.type B.type C.type
  leftUnitor A := leftUnit_pure A.type
  leftUnitor_inv A := leftUnitInv_pure A.type
  rightUnitor A := rightUnit_pure A.type
  rightUnitor_inv A := rightUnitInv_pure A.type
  braiding A B := swap_pure A.type B.type
  exchange p := tensor_exchange hR p

/-- The premonoidal structure on literal signature types, with every
coherence proof filled by the native calculus. -/
@[instance_reducible] def typePremonoidal :
    letI := category (ε := ε) F R hR
    PremonoidalCategory τ :=
  typePremonoidalOfPentagon hR (fun A B C D => pentagon hR A.type B.type C.type D.type)

@[instance_reducible] def typeSymmetric :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
    SymmetricPremonoidalCategory τ := by
  letI := category (ε := ε) F R hR
  letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
  exact
    { braiding := swapIso hR
      naturality_left := fun f C => swap_right_natural hR f C
      naturality_right := fun A _ _ f => swap_left_natural hR A f
      hexagon_forward := hexagon_forward hR
      hexagon_reverse := hexagon_reverse hR
      braiding_central := by
        intro A B
        constructor
        · intro C D g
          exact pure_exchange_left hR (swap_pure A B) g
        · intro C D g
          exact pure_exchange_right hR g (swap_pure A B)
      symmetry := swap_swap hR }

/-- Hom orders on literal types are the quotient refinement orders. -/
@[instance_reducible] def typeHomOrder :
    letI := category (ε := ε) F R hR
    ∀ A B : τ, PartialOrder (A ⟶ B) :=
  fun A B => inferInstanceAs (PartialOrder (Hom (ε := ε) F R A B))

theorem typeOrderedPremonoidal :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
    letI := typeHomOrder (F := F) (R := R) (ε := ε) hR
    OrderedPremonoidal τ := by
  let := category (ε := ε) F R hR
  let := typePremonoidal (F := F) (R := R) (ε := ε) hR
  let := typeHomOrder (F := F) (R := R) (ε := ε) hR
  exact
    { comp_mono := compose_mono hR
      whiskerLeft_mono := by
        intro A B C f g h
        exact left_mono hR A h
      whiskerRight_mono := by
        intro A B f g D h
        exact right_mono hR D h }

/-- The same effect predicate and exchange theorem on literal signature types. -/
def typeEffects :
    letI := category (ε := ε) F R hR
    letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
    letI := typeSymmetric (F := F) (R := R) (ε := ε) hR
    letI := typeHomOrder (F := F) (R := R) (ε := ε) hR
    EffectfulCategory τ ε := by
  letI := category (ε := ε) F R hR
  letI := typePremonoidal (F := F) (R := R) (ε := ε) hR
  letI := typeSymmetric (F := F) (R := R) (ε := ε) hR
  letI := typeHomOrder (F := F) (R := R) (ε := ε) hR
  exact
    { effect := fun e _ _ f => hasEffect e f
      mono := fun h _ _ _ hf => hasEffect_mono h hf
      top := hasEffect_top
      id := fun _ A => hasEffect_mono bot_le (identity_pure A)
      comp := compose_effect hR
      whiskerLeft := by
        intro e A B C f h
        exact left_effect hR A h
      whiskerRight := by
        intro e A B f D h
        exact right_effect hR D h
      associator := assoc_pure
      associator_inv := assocInv_pure
      leftUnitor := leftUnit_pure
      leftUnitor_inv := leftUnitInv_pure
      rightUnitor := rightUnit_pure
      rightUnitor_inv := rightUnitInv_pure
      braiding := swap_pure
      exchange := by
        intro p e η A B C D f g hm hf hg
        exact tensor_exchange hR p hm hf hg }

end Silmaril.Isotope.Refinement.Models.Syntactic
