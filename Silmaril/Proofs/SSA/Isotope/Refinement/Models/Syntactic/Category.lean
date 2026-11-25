module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Syntactic.Operations
public import Silmaril.Raw.SSA.Isotope.Refinement.Structural
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Structures

/-! # Composition and enrichment of the written syntactic category

The primitive theory must be stable under resource-valid renaming. This explicit
hypothesis is sufficient to descend sequential composition to mutual refinement.
The identities and associativity below are derived from the native written rules.
-/

@[expose] public section

noncomputable section

universe u v w

namespace Silmaril.Isotope.Refinement.Models.Syntactic

open CategoryTheory

variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type v} [HasTy Φ τ]
variable {ε : Type w} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} {R : Relation τ Φ} {A B C D : τ}

/-- Sequential congruence includes the resource-valid insertion of the old input. -/
theorem compose_refines (hR : R.RenamingClosed)
    {a a' : Arrow (Φ := Φ) (ε := ε) F A B} {b b' : Arrow (Φ := Φ) (ε := ε) F B C}
    (ha : Refines (ε := ε) F R (input A) a.val a'.val B)
    (hb : Refines (ε := ε) F R (input B) b.val b'.val C) :
    Refines (ε := ε) F R (input A) (composeArrow a b).val (composeArrow a' b').val C :=
  .let₁ (inputSplit A) ha
    (hb.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up B) hR)

theorem compose_equates (hR : R.RenamingClosed)
    {a a' : Arrow (Φ := Φ) (ε := ε) F A B} {b b' : Arrow (Φ := Φ) (ε := ε) F B C}
    (ha : Equates (ε := ε) F R (input A) a.val a'.val B)
    (hb : Equates (ε := ε) F R (input B) b.val b'.val C) :
    Equates (ε := ε) F R (input A) (composeArrow a b).val (composeArrow a' b').val C :=
  ⟨compose_refines hR ha.1 hb.1, compose_refines hR ha.2 hb.2⟩

/-- Composition is induced by let, not by an unrestricted substitution operation. -/
def compose (hR : R.RenamingClosed)
    (a : Hom (ε := ε) F R A B) (b : Hom (ε := ε) F R B C) : Hom (ε := ε) F R A C :=
  Quotient.map₂ composeArrow (fun _ _ ha _ _ hb => compose_equates hR ha hb) a b

@[simp] theorem compose_ofArrow (hR : R.RenamingClosed)
    (a : Arrow (Φ := Φ) (ε := ε) F A B) (b : Arrow (Φ := Φ) (ε := ε) F B C) :
    compose (R := R) hR (ofArrow a) (ofArrow b) = ofArrow (composeArrow a b) := rfl

theorem identity_compose (hR : R.RenamingClosed) (a : Hom (ε := ε) F R A B) :
    compose hR (identity A) a = a := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (identity_compose_equates R a)

theorem compose_identity (hR : R.RenamingClosed) (a : Hom (ε := ε) F R A B) :
    compose hR a (identity B) = a := by
  induction a using Quotient.inductionOn with
  | _ a => exact Quotient.sound (compose_identity_equates R a)

theorem compose_assoc (hR : R.RenamingClosed) (a : Hom (ε := ε) F R A B)
    (b : Hom (ε := ε) F R B C) (c : Hom (ε := ε) F R C D) :
    compose hR (compose hR a b) c = compose hR a (compose hR b c) := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c => exact Quotient.sound (compose_assoc_equates R a b c)

theorem compose_mono (hR : R.RenamingClosed)
    {a a' : Hom (ε := ε) F R A B} {b b' : Hom (ε := ε) F R B C}
    (ha : a ≤ a') (hb : b ≤ b') : compose hR a b ≤ compose hR a' b' := by
  induction a, a' using Quotient.inductionOn₂ with
  | _ a a' =>
    induction b, b' using Quotient.inductionOn₂ with
    | _ b b' => exact compose_refines hR ha hb

theorem compose_effect (hR : R.RenamingClosed) {e : ε}
    {a : Hom (ε := ε) F R A B} {b : Hom (ε := ε) F R B C}
    (ha : hasEffect e a) (hb : hasEffect e b) : hasEffect e (compose hR a b) := by
  obtain ⟨a, rfl, ⟨da⟩⟩ := ha
  obtain ⟨b, rfl, ⟨db⟩⟩ := hb
  exact ⟨composeArrow a b, rfl, ⟨composeDeriv da db⟩⟩

/-- The native category on the signature's types, for use in semantic bundles. -/
@[instance_reducible] def category (F : Fragment) (R : Relation τ Φ) (hR : R.RenamingClosed) : Category τ where
  Hom := Hom (ε := ε) F R
  id := identity
  comp := compose hR
  id_comp := identity_compose hR
  comp_id := compose_identity hR
  assoc := compose_assoc hR

/-- A type wrapper allows several syntactic theories to coexist as categories. -/
structure Object (ε : Type w) (F : Fragment) (R : Relation τ Φ)
    (hR : R.RenamingClosed) where
  type : τ

instance (hR : R.RenamingClosed) : Category (Object ε F R hR) where
  Hom A B := Hom (ε := ε) F R A.type B.type
  id A := identity A.type
  comp := compose hR
  id_comp := identity_compose hR
  comp_id := compose_identity hR
  assoc := compose_assoc hR

instance (hR : R.RenamingClosed) (A B : Object ε F R hR) : PartialOrder (A ⟶ B) :=
  inferInstanceAs (PartialOrder (Hom (ε := ε) F R A.type B.type))

instance (hR : R.RenamingClosed) : OrderedCategory (Object ε F R hR) where
  comp_mono := compose_mono hR

end Silmaril.Isotope.Refinement.Models.Syntactic
