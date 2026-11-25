module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.Product.Extensionality.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs

/-! # Terminal and binary-product criteria for Paper values -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (productFstBranches productSndBranches)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory (τ := τ) Φ
local notation "paperObj" => ofType (τ := τ) (Φ := Φ)

theorem discard_comp_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    PreservesDiscard (ofRegion (.br (ℓ := 0) rfl ha)) := by
  change ofRegion (.br (ℓ := 0) rfl ha) ≫ discardArrow (τ := τ) (Φ := Φ) A = discardArrow (τ := τ) (Φ := Φ) X
  let hr : ValueBranches [X] (.br 0 a) [A] := .br rfl ha
  let hs : ValueBranches [A] (.br 0 (.unit : Tm Φ)) [Silmaril.unit] := .br rfl .unit
  change ofRegion hr ≫ ofRegion hs = _
  rw [ofRegion_comp hr hs (CfgEta.TypeCategory.seqValueBranches hr hs)]
  rfl

theorem discard_unit_eq_id_iff :
    discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ↔
      Paper.Eqv [(Silmaril.unit : τ)] (.br 0 (.unit : Tm Φ)) (.br 0 (.var 0)) [Silmaril.unit] := by
  rw [← ofRegion_eq_iff (.br (ℓ := 0) rfl (.unit (Γ := [(Silmaril.unit : τ)])))
    (.br (ℓ := 0) rfl (.var (i := 0) (rfl : At [(Silmaril.unit : τ)] 0 (Silmaril.unit : τ)))),
    ofRegion_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem wideUnit_isTerminal_iff (P : MorphismProperty Comp) [P.IsMultiplicative]
    (hasDiscard : ∀ X : τ, P (discardArrow (Φ := Φ) X)) :
    Nonempty (IsTerminal (⟨paperObj Silmaril.unit⟩ : WideSubcategory P)) ↔
      discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ∧ P ≤ PreservesDiscard := by
  let drop (X : WideSubcategory P) : X ⟶ ⟨paperObj Silmaril.unit⟩ :=
    ⟨discardArrow (Φ := Φ) (show τ from X.obj), hasDiscard _⟩
  constructor
  · rintro ⟨h⟩
    refine ⟨congrArg (·.1) (h.hom_ext (drop _) (𝟙 _)), ?_⟩
    intro X Y f hf
    exact congrArg (·.1) (h.hom_ext (⟨f, hf⟩ ≫ drop ⟨Y⟩) (drop ⟨X⟩))
  · rintro ⟨idDiscard, discard⟩
    refine ⟨IsTerminal.ofUniqueHom drop ?_⟩
    intro X f
    apply WideSubcategory.hom_ext
    have hf : PreservesDiscard f.1 := discard _ f.2
    change f.1 ≫ discardArrow (τ := τ) (Φ := Φ) _ = _ at hf
    rw [idDiscard, Category.comp_id] at hf
    exact hf

variable {ε : Type w} [HasEff Φ ε] (pe : ε)

theorem copyingPureReturn_branchValue {X A : τ} {a : Tm Φ} (ha : Tm.BranchValue [X] a A) :
    CopyingPureReturn pe (ofRegion (.br (ℓ := 0) rfl ha)) :=
  ⟨centralPureReturn_branchValue pe ha, pairArrows_copy_branchValue ha⟩

theorem centralUnit_isTerminal_iff :
    Nonempty (IsTerminal (⟨paperObj Silmaril.unit⟩ : CentralValueCategory (τ := τ) (Φ := Φ) pe)) ↔
      discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ∧
        CentralPureReturn (τ := τ) (Φ := Φ) pe ≤ PreservesDiscard :=
  wideUnit_isTerminal_iff _ (fun X => centralPureReturn_branchValue pe (.unit (Γ := [X])))

theorem copyingUnit_isTerminal_iff :
    Nonempty (IsTerminal (⟨paperObj Silmaril.unit⟩ : CopyingValueCategory (τ := τ) (Φ := Φ) pe)) ↔
      discardArrow (Φ := Φ) (Silmaril.unit : τ) = 𝟙 _ ∧
        CopyingPureReturn (τ := τ) (Φ := Φ) pe ≤ PreservesDiscard :=
  wideUnit_isTerminal_iff _ (fun X => copyingPureReturn_branchValue pe (.unit (Γ := [X])))

set_option hygiene false in
local notation "Values" => CopyingValueCategory (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false in
theorem copyingProduct_isLimit_iff (A B : τ)
    (fst : CopyingPureReturn pe (ofRegion (τ := τ) (productFstBranches (Φ := Φ) A B)))
    (snd : CopyingPureReturn pe (ofRegion (τ := τ) (productSndBranches (Φ := Φ) A B))) :
    Nonempty (IsLimit (copyingProductFan pe A B fst snd)) ↔
      ∀ {X : Values} (f : X ⟶ ⟨paperObj A⟩) (g : X ⟶ ⟨paperObj B⟩),
        let p := pairArrows (τ := τ) (Φ := Φ) f.1 g.1
        CopyingPureReturn pe p ∧
          p ≫ ofRegion (τ := τ) (productFstBranches A B) = f.1 ∧
          p ≫ ofRegion (τ := τ) (productSndBranches A B) = g.1 := by
  constructor
  · rintro ⟨h⟩ X f g
    let cone := BinaryFan.mk f g
    let p := h.lift cone
    have hl : p.1 ≫ ofRegion (τ := τ) (productFstBranches A B) = f.1 :=
      congrArg (·.1) (h.fac cone ⟨WalkingPair.left⟩)
    have hr : p.1 ≫ ofRegion (τ := τ) (productSndBranches A B) = g.1 :=
      congrArg (·.1) (h.fac cone ⟨WalkingPair.right⟩)
    have hp := pairArrows_projections_of_preservesDiagonal (τ := τ) p.1 p.2.2
    rw [hl, hr] at hp
    dsimp only
    rw [hp]
    exact ⟨p.2, hl, hr⟩
  · intro close
    let lift {X : Values} (f : X ⟶ ⟨paperObj A⟩) (g : X ⟶ ⟨paperObj B⟩) :
        X ⟶ (copyingProductFan pe A B fst snd).pt :=
      ⟨pairArrows (τ := τ) f.1 g.1, (close f g).1⟩
    refine ⟨BinaryFan.IsLimit.mk _ (@lift) ?_ ?_ ?_⟩
    · intro X f g
      exact WideSubcategory.hom_ext _ (close f g).2.1
    · intro X f g
      exact WideSubcategory.hom_ext _ (close f g).2.2
    · intro X f g p hl hr
      apply WideSubcategory.hom_ext
      exact projection_ext_of_preservesDiagonal (τ := τ) p.2.2 (lift f g).2.2
        ((congrArg (·.1) hl).trans (close f g).2.1.symm)
        ((congrArg (·.1) hr).trans (close f g).2.2.symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CartesianValueBoundary
