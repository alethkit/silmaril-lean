module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Sequential
public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Structure

/-! # Tensor actions on interpreted representatives -/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable {F : Fragment} (M : SeqModel.{u,v,w,r} τ Φ ε) (K : ControlData M.toSeqData F)

theorem split_pairContext (P A B : τ) :
    split M.toSeqData (Syntactic.pairSplit P A B) =
      M.compose (M.right (M.rightUnitorInv (product Silmaril.unit A)) B)
        (M.associator (product Silmaril.unit A) Silmaril.unit B) := by
  have hs : split M.toSeqData
      ((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := A) (.left (.used ⊤))) =
      M.rightUnitorInv (product Silmaril.unit A) :=
    eq_of_heq (split_zero_right M.toSeqData ((QCtx.nil.snoc P .zero).snoc A))
  change M.compose (M.right (split M.toSeqData
      ((QCtx.Split.nil.snoc (A := P) (.left .zero)).snoc (A := A) (.left (.used ⊤)))) B)
    (M.associator (product Silmaril.unit A) Silmaril.unit B) = _
  exact congrArg (fun f : M.Hom (product Silmaril.unit A) (product (product Silmaril.unit A) Silmaril.unit) =>
    M.compose (M.right f B) (M.associator (product Silmaril.unit A) Silmaril.unit B)) hs

theorem leftUnit_input (A : τ) :
    M.compose (M.leftUnitorInv A)
      (M.compose (M.leftUnitorInv (product Silmaril.unit A)) (M.left Silmaril.unit (M.leftUnitor A))) =
      M.leftUnitorInv A := by
  let A' : M.toSeqData.PureObject := ⟨A⟩
  have h : (λ_ A').inv ≫ (λ_ (𝟙_ M.toSeqData.PureObject ⊗ A')).inv ≫
      (𝟙_ M.toSeqData.PureObject) ◁ (λ_ A').hom = (λ_ A').inv := by monoidal
  exact congrArg Subtype.val h

theorem pair_input_left (P A B : τ) :
    M.compose (M.leftUnitorInv (product A B))
      (M.compose (M.associatorInv Silmaril.unit A B)
        (M.compose (split M.toSeqData (Syntactic.pairSplit P A B))
          (M.right (M.leftUnitor A) (product Silmaril.unit B)))) =
      M.left A (M.leftUnitorInv B) := by
  rw [split_pairContext]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  have h : (λ_ (A' ⊗ B')).inv ≫ (α_ (𝟙_ M.toSeqData.PureObject) A' B').inv ≫
      ((ρ_ ((𝟙_ M.toSeqData.PureObject) ⊗ A')).inv ▷ B' ≫
        (α_ ((𝟙_ M.toSeqData.PureObject) ⊗ A') (𝟙_ M.toSeqData.PureObject) B').hom) ≫
      (λ_ A').hom ▷ ((𝟙_ M.toSeqData.PureObject) ⊗ B') = A' ◁ (λ_ B').inv := by monoidal
  exact congrArg Subtype.val h

theorem pair_input_right (P A B : τ) :
    M.compose (M.leftUnitorInv (product A B))
      (M.compose (M.associatorInv Silmaril.unit A B)
        (M.compose (split M.toSeqData (Syntactic.pairSplit P A B))
          (M.left (product Silmaril.unit A) (M.leftUnitor B)))) =
      M.right (M.leftUnitorInv A) B := by
  rw [split_pairContext]
  let A' : M.toSeqData.PureObject := ⟨A⟩
  let B' : M.toSeqData.PureObject := ⟨B⟩
  have h : (λ_ (A' ⊗ B')).inv ≫ (α_ (𝟙_ M.toSeqData.PureObject) A' B').inv ≫
      ((ρ_ ((𝟙_ M.toSeqData.PureObject) ⊗ A')).inv ▷ B' ≫
        (α_ ((𝟙_ M.toSeqData.PureObject) ⊗ A') (𝟙_ M.toSeqData.PureObject) B').hom) ≫
      ((𝟙_ M.toSeqData.PureObject) ⊗ A') ◁ (λ_ B').hom = (λ_ A').inv ▷ B' := by monoidal
  exact congrArg Subtype.val h

variable (N : ControlEnvironment K) (H : WitnessCoherent M K)
include N H

theorem denote_onRight {A B C P : τ} {e : ε} {a : Term Φ 1}
    (ha : HasType F (Syntactic.input B) e a C) :
    Denotation.denote M.toSeqData K
      (ha.rename _ (.cons (.skip (.skip (.refl QCtx.nil) (A := P) (q := .zero) le_rfl) (A := A) (q := .zero) le_rfl) le_rfl)) =
        Denotation.denote M.toSeqData K ha := by
  have hu : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  let w := (QCtx.Weakening.cons (.skip (.skip (.refl (QCtx.nil : QCtx τ 0)) (A := P) (q := .zero) le_rfl)
    (A := A) (q := .zero) le_rfl) (A := B) (q := .used ⊤) (q' := .used ⊤) le_rfl)
  have hw : weaken M.toSeqData w = M.identity (product Silmaril.unit B) := by
    change M.right (M.discard Silmaril.unit hu) B = _
    rw [M.discard_unit, M.toSeqData.right_identity]
  have hd := denote_rename_of_typing M K N H ha _ w (ha.rename _ w)
  exact hd.trans ((congrArg (fun f : M.Hom (product Silmaril.unit B) (product Silmaril.unit B) =>
    M.compose f (Denotation.denote M.toSeqData K ha)) hw).trans (M.identity_compose _))

theorem denote_onLeft {A B C P : τ} {e : ε} {a : Term Φ 1}
    (ha : HasType F (Syntactic.input A) e a B) :
    Denotation.denote M.toSeqData K
      (ha.rename _ (.skip (.cons (.skip (.refl QCtx.nil) (A := P) (q := .zero) le_rfl) le_rfl) (A := C) (q := .zero) le_rfl)) =
        Denotation.denote M.toSeqData K ha := by
  have hu : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  let w := (QCtx.Weakening.skip (.cons (.skip (.refl (QCtx.nil : QCtx τ 0)) (A := P) (q := .zero) le_rfl)
    (A := A) (q := .used ⊤) (q' := .used ⊤) le_rfl) (A := C) (q := .zero) le_rfl)
  have hw : weaken M.toSeqData w = M.identity (product Silmaril.unit A) := by
    change M.right (M.discard Silmaril.unit hu) A = _
    rw [M.discard_unit, M.toSeqData.right_identity]
  have hd := denote_rename_of_typing M K N H ha _ w (ha.rename _ w)
  exact hd.trans ((congrArg (fun f : M.Hom (product Silmaril.unit A) (product Silmaril.unit A) =>
    M.compose f (Denotation.denote M.toSeqData K ha)) hw).trans (M.identity_compose _))

theorem denoteArrow_leftDeriv (A : τ) {B C : τ} {e : ε} {a : Term Φ 1}
    (ha : HasType F (Syntactic.input B) e a C) :
    denoteArrow M.toSeqData K (Syntactic.leftDeriv A ha) =
      M.left A (denoteArrow M.toSeqData K ha) := by
  let d : M.Hom (product Silmaril.unit B) C := Denotation.denote M.toSeqData K ha
  let di : M.Hom (product Silmaril.unit (product A B)) (product A B) :=
    Denotation.denote M.toSeqData K (Syntactic.identityDeriv (product A B) e)
  let dl : M.Hom (product Silmaril.unit A) A :=
    Denotation.denote M.toSeqData K (Syntactic.leftParameter (product A B) A B e)
  let dr : M.Hom (product Silmaril.unit B) C := Denotation.denote M.toSeqData K
    (ha.rename _ (.cons (.skip (.skip (.refl QCtx.nil) (A := product A B) (q := .zero) le_rfl)
      (A := A) (q := .zero) le_rfl) le_rfl))
  let si : M.Hom (product Silmaril.unit (product A B)) (product Silmaril.unit (product Silmaril.unit (product A B))) :=
    split M.toSeqData (Syntactic.inputSplit (product A B))
  let sp : M.Hom (product (product Silmaril.unit A) B) (product (product Silmaril.unit A) (product Silmaril.unit B)) :=
    split M.toSeqData (Syntactic.pairSplit (product A B) A B)
  have hdi : di = M.leftUnitor (product A B) := denote_identityDeriv M K _ _
  have hdl : dl = M.leftUnitor A := denote_leftParameter M K _ _ _ _
  have hdr : dr = d := denote_onRight M K N H (P := product A B) (A := A) ha
  have hsi : si = M.leftUnitorInv (product Silmaril.unit (product A B)) :=
    eq_of_heq (split_zero_left M.toSeqData (Syntactic.input (product A B)))
  change M.compose (M.leftUnitorInv (product A B))
    (M.compose si (M.compose (M.left Silmaril.unit di)
      (M.compose (M.associatorInv Silmaril.unit A B) (M.compose sp (M.tensor dl dr))))) =
        M.left A (M.compose (M.leftUnitorInv B) d)
  rw [hdi, hdl, hdr, hsi]
  have hui := leftUnit_input M (product A B)
  rw [← M.compose_assoc] at hui
  rw [← M.compose_assoc, ← M.compose_assoc, hui]
  rw [SeqData.tensor, ← M.compose_assoc _ _ (M.left A d),
    ← M.compose_assoc _ _ (M.left A d), ← M.compose_assoc _ _ (M.left A d)]
  change M.compose (M.compose (M.leftUnitorInv (product A B))
    (M.compose (M.associatorInv Silmaril.unit A B)
      (M.compose (split M.toSeqData (Syntactic.pairSplit (product A B) A B))
        (M.right (M.leftUnitor A) (product Silmaril.unit B))))) (M.left A d) = _
  rw [pair_input_left, ← M.toSeqData.left_compose]

theorem denoteArrow_rightDeriv {A B : τ} (C : τ) {e : ε} {a : Term Φ 1}
    (ha : HasType F (Syntactic.input A) e a B) :
    denoteArrow M.toSeqData K (Syntactic.rightDeriv C ha) =
      M.right (denoteArrow M.toSeqData K ha) C := by
  let d : M.Hom (product Silmaril.unit A) B := Denotation.denote M.toSeqData K ha
  let di : M.Hom (product Silmaril.unit (product A C)) (product A C) :=
    Denotation.denote M.toSeqData K (Syntactic.identityDeriv (product A C) e)
  let dl : M.Hom (product Silmaril.unit A) B := Denotation.denote M.toSeqData K
    (ha.rename _ (.skip (.cons (.skip (.refl QCtx.nil) (A := product A C) (q := .zero) le_rfl)
      le_rfl) (A := C) (q := .zero) le_rfl))
  let dr : M.Hom (product Silmaril.unit C) C :=
    Denotation.denote M.toSeqData K (Syntactic.rightParameter (product A C) A C e)
  let si : M.Hom (product Silmaril.unit (product A C)) (product Silmaril.unit (product Silmaril.unit (product A C))) :=
    split M.toSeqData (Syntactic.inputSplit (product A C))
  let sp : M.Hom (product (product Silmaril.unit A) C) (product (product Silmaril.unit A) (product Silmaril.unit C)) :=
    split M.toSeqData (Syntactic.pairSplit (product A C) A C)
  have hdi : di = M.leftUnitor (product A C) := denote_identityDeriv M K _ _
  have hdl : dl = d := denote_onLeft M K N H (P := product A C) (C := C) ha
  have hdr : dr = M.leftUnitor C := denote_rightParameter M K _ _ _ _
  have hsi : si = M.leftUnitorInv (product Silmaril.unit (product A C)) :=
    eq_of_heq (split_zero_left M.toSeqData (Syntactic.input (product A C)))
  change M.compose (M.leftUnitorInv (product A C))
    (M.compose si (M.compose (M.left Silmaril.unit di)
      (M.compose (M.associatorInv Silmaril.unit A C) (M.compose sp (M.tensor dl dr))))) =
        M.right (M.compose (M.leftUnitorInv A) d) C
  rw [hdi, hdl, hdr, hsi]
  have hui := leftUnit_input M (product A C)
  rw [← M.compose_assoc] at hui
  rw [← M.compose_assoc, ← M.compose_assoc, hui]
  rw [SeqData.tensor, M.toSeqData.exchange_right_pure d (M.leftUnitor C) (M.toSeqData.leftUnitor_pure C)]
  rw [← M.compose_assoc _ _ (M.right d C), ← M.compose_assoc _ _ (M.right d C),
    ← M.compose_assoc _ _ (M.right d C)]
  change M.compose (M.compose (M.leftUnitorInv (product A C))
    (M.compose (M.associatorInv Silmaril.unit A C)
      (M.compose (split M.toSeqData (Syntactic.pairSplit (product A C) A C))
        (M.left (product Silmaril.unit A) (M.leftUnitor C))))) (M.right d C) = _
  rw [pair_input_right, ← M.toSeqData.right_compose]

end Silmaril.Isotope.Refinement.Models.Interpretation
