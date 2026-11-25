module

public import Silmaril.Proofs.SSA.Isotope.Refinement.Models.Interpretation.Control
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.IterationCoherence
public import Silmaril.Raw.SSA.Isotope.Refinement.Models.Denotation.ControlEnvironment

/-! # Interpretation of the native iteration representative

An empty retained environment contributes only the unit coherence maps. Pure
uniformity removes that padding, yielding the model's chosen iteration.
-/

@[expose] public section
noncomputable section
namespace Silmaril.Isotope.Refinement.Models.Interpretation
open Denotation CategoryTheory
open scoped MonoidalCategory
universe u v w r
variable {τ : Type u} [TypeFormers τ] [TypeQuantity τ]
variable {Φ : Type w} [HasTy Φ τ] {ε : Type r} [EffectSystem ε] [HasEff Φ ε]
variable (M : IterModel.{u,v,w,r} τ Φ ε)

/-- The contextual step at the unit environment only inserts the next-state padding. -/
theorem unit_contextStep {A B : τ}
    (hc : Quantity.relevant ≤ quantity (Silmaril.unit : τ))
    (hd : Quantity.affine ≤ quantity (Silmaril.unit : τ))
    (f : M.Hom (product Silmaril.unit A) (coprod B A)) :
    (ControlData.iter M).contextStep trivial Silmaril.unit hc hd f =
      M.compose f (M.desc (M.inl B (product Silmaril.unit A))
        (M.compose (M.leftUnitorInv A) (M.inr B (product Silmaril.unit A)))) := by
  have hp : M.compose (M.right (M.leftUnitorInv Silmaril.unit) A)
      (M.associator Silmaril.unit Silmaril.unit A) = M.leftUnitorInv (product Silmaril.unit A) := by
    let A' : M.toSeqData.PureObject := ⟨A⟩
    let I : M.toSeqData.PureObject := 𝟙_ M.toSeqData.PureObject
    have h : (λ_ I).inv ▷ A' ≫ (α_ I I A').hom = (λ_ (I ⊗ A')).inv := by monoidal
    exact congrArg Subtype.val h
  have hn : M.compose (M.leftUnitorInv (product Silmaril.unit A)) (M.left Silmaril.unit f) =
      M.compose f (M.leftUnitorInv (coprod B A)) := by
    have h := congrArg (fun g => M.compose g (M.leftUnitorInv (coprod B A)))
      (M.toSeqData.unit_bind f)
    simpa only [M.compose_assoc, M.toSeqData.leftUnitor_hom_inv, M.compose_identity] using h
  simp only [ControlData.contextStep, ControlData.iter, ControlData.ofCase,
    M.copy_unit, M.discard_unit, M.toSeqData.right_identity, M.identity_compose]
  rw [← M.compose_assoc, hp, ← M.compose_assoc, hn, M.compose_assoc,
    unit_desc M.toCaseData]
  simp only [← M.compose_assoc, M.toSeqData.leftUnitor_inv_hom, M.identity_compose]

/-- Removing the unit state padding commutes with actual categorical iteration. -/
theorem unit_iterateWithContext {A B : τ}
    (hc : Quantity.relevant ≤ quantity (Silmaril.unit : τ))
    (hd : Quantity.affine ≤ quantity (Silmaril.unit : τ))
    (f : M.Hom (product Silmaril.unit A) (coprod B A)) :
    M.compose (M.leftUnitorInv A)
      ((ControlData.iter M).iterateWithContext trivial Silmaril.unit hc hd f) =
      M.iterate (M.compose (M.leftUnitorInv A) f) := by
  apply M.pure_uniformity (M.toSeqData.leftUnitorInv_pure A)
  rw [unit_contextStep, M.compose_assoc]

/-- The native singleton loop denotes the model's designated iteration. -/
theorem denoteArrow_iterateDeriv (H : WitnessCoherent M.toSeqModel (ControlData.iter M))
    {A B : τ} {e : ε} (he : EffectSystem.iterable e) {a : Term Φ 1}
    (ha : HasType .iter (Syntactic.input A) e a (coprod B A)) :
    denoteArrow M.toSeqData (ControlData.iter M) (Syntactic.iterateDeriv (F := .iter) trivial he ha) =
      M.iterate (denoteArrow M.toSeqData (ControlData.iter M) ha) := by
  let K := ControlData.iter M
  let d : M.Hom (product Silmaril.unit A) (coprod B A) := Denotation.denote M.toSeqData K ha
  let di : M.Hom (product Silmaril.unit A) A :=
    Denotation.denote M.toSeqData K (Syntactic.identityDeriv A e)
  let db : M.Hom (product Silmaril.unit A) (coprod B A) :=
    Denotation.denote M.toSeqData K (ha.rename _ ((QCtx.Weakening.insertZero QCtx.nil A).up A))
  let si : M.Hom (product Silmaril.unit A) (product Silmaril.unit (product Silmaril.unit A)) :=
    split M.toSeqData (Syntactic.inputSplit A)
  have hi : di = M.leftUnitor A := denote_identityDeriv M.toSeqModel K _ _
  have hb : db = d := denote_continuation M.toSeqModel K (ControlEnvironment.iter M) H ha
  have hs : si = M.leftUnitorInv (product Silmaril.unit A) :=
    eq_of_heq (split_zero_left M.toSeqData (Syntactic.input A))
  have hc : Quantity.relevant ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  have hd : Quantity.affine ≤ quantity (Silmaril.unit : τ) := by
    rw [TypeQuantity.unit_quantity]; exact le_top
  change M.compose (M.leftUnitorInv A)
    (M.compose si (M.compose (M.left Silmaril.unit di)
      ((ControlData.iter M).iterateWithContext trivial Silmaril.unit hc hd db))) =
        M.iterate (M.compose (M.leftUnitorInv A) d)
  rw [hi, hb, hs]
  have hu : M.compose (M.leftUnitorInv (product Silmaril.unit A)) (M.left Silmaril.unit (M.leftUnitor A)) =
      M.identity (product Silmaril.unit A) := by
    let A' : M.toSeqData.PureObject := ⟨A⟩
    have h : (λ_ (𝟙_ M.toSeqData.PureObject ⊗ A')).inv ≫
      (𝟙_ M.toSeqData.PureObject) ◁ (λ_ A').hom = 𝟙 (𝟙_ M.toSeqData.PureObject ⊗ A') := by monoidal
    exact congrArg Subtype.val h
  rw [← M.compose_assoc (M.leftUnitorInv (product Silmaril.unit A)), hu, M.identity_compose]
  exact unit_iterateWithContext M hc hd d

end Silmaril.Isotope.Refinement.Models.Interpretation
