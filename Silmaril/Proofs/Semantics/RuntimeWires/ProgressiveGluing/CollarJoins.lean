module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram
open Diagram.OrderedVerticalMatch (collarCount collarIndex)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : Diagram S L A .point} {upper : Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

theorem bottom_inside (w : PartialVerticalMatch.Contact lower) : lower.x w.val 1 ∈ Set.Ioo 0 1 := by
  have hi : lower.upper w.val = 1 := by simp [Diagram.upper, endpointHeight, w.property]
  have h : lower.covers w.val 1 :=
    ⟨hi ▸ (lower.wire w.val).increasing.le, hi.ge⟩
  exact lower.wire_inside w.val 1 h

theorem top_inside (w : {w : Fin B // upper.start w = none}) : upper.x w.val 0 ∈ Set.Ioo 0 1 := by
  have lo : upper.lower w.val = 0 := by simp [Diagram.lower, endpointHeight, w.property]
  have h : upper.covers w.val 0 :=
    ⟨lo.le, lo ▸ (upper.wire w.val).increasing.le⟩
  exact upper.wire_inside w.val 0 h

noncomputable def matchCollar : CollarSpec O (collarCount lower) where
  label i := lower.label ((collarIndex lower).symm i).val
  bottom i := lower.x ((collarIndex lower).symm i).val 1
  top i := upper.x (m.contact ((collarIndex lower).symm i)).val 0
  bottom_inside i := bottom_inside ((collarIndex lower).symm i)
  top_inside i := top_inside (m.contact ((collarIndex lower).symm i))
  bottom_injective := by
    intro i j same
    by_contra ne
    let a := (collarIndex lower).symm i
    let b := (collarIndex lower).symm j
    have distinct : a.val ≠ b.val := fun h => ne ((collarIndex lower).symm.injective (Subtype.ext h))
    exact lower.output_boundary_separated distinct a.property b.property same
  order a b := m.order _ _

noncomputable def collar : Diagram S 0 (collarCount lower) .point := (matchCollar m).drawing S

def allCap {W : ℕ} {P : Fin W → Prop} (h : ∀ i, P i) : Fin W ≃ {i : Fin W // P i} where
  toFun i := ⟨i, h i⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def lowerJoin : lower.PartialVerticalMatch (collar m) where
  contact := (collarIndex lower).trans (allCap fun i => (matchCollar m).drawing_start i)
  label w := by
    change lower.label w.val = ((matchCollar m).drawing S).label (collarIndex lower w)
    rw [(matchCollar m).drawing_label]
    change lower.label w.val = lower.label ((collarIndex lower).symm (collarIndex lower w)).val
    rw [Equiv.symm_apply_apply]
  coordinate w := by
    change lower.x w.val 1 = ((matchCollar m).drawing S).x (collarIndex lower w) 0
    rw [(matchCollar m).drawing_bottom]
    change lower.x w.val 1 = lower.x ((collarIndex lower).symm (collarIndex lower w)).val 1
    rw [Equiv.symm_apply_apply]

noncomputable def collarUpperContact : {w : Fin (collarCount lower) // (collar m).finish w = none} ≃
    {w : Fin B // upper.start w = none} where
  toFun w := m.contact ((collarIndex lower).symm w.val)
  invFun w :=
    ⟨collarIndex lower (m.contact.symm w), (matchCollar m).drawing_finish _⟩
  left_inv _ := by
    apply Subtype.ext
    simp
  right_inv _ := by simp

theorem collarUpper_label (w : {w : Fin (collarCount lower) // (collar m).finish w = none}) :
    (collar m).label w.val = upper.label (collarUpperContact m w).val :=
  ((matchCollar m).drawing_label w.val).trans (m.label ((collarIndex lower).symm w.val))

theorem collarUpper_x (w : {w : Fin (collarCount lower) // (collar m).finish w = none}) :
    (collar m).x w.val 1 = upper.x (collarUpperContact m w).val 0 :=
  (matchCollar m).drawing_top w.val

noncomputable def upperCapEquiv (j : lower.PartialVerticalMatch upper) :
    {w : Fin B // upper.finish w = none} ≃
      {z : Fin (PartialVerticalMatch.wireCount lower upper) // j.glue.finish z = none} :=
  Equiv.ofBijective
    (fun w => ⟨j.upperId w.val, by rw [j.glue_finish_upper, w.property]; rfl⟩)
    ⟨fun _ _ e => Subtype.ext (j.upperId_injective (congrArg Subtype.val e)), fun z => by
      obtain ⟨w, cap, eq⟩ := j.glue_output_cap_exists z.property
      exact ⟨⟨w, cap⟩, Subtype.ext eq⟩⟩

theorem upperCap_label (j : lower.PartialVerticalMatch upper) (w : {w : Fin B // upper.finish w = none}) :
    j.glue.label (upperCapEquiv j w).val = upper.label w.val :=
  j.glue_label_upper w.val

theorem upperCap_x (j : lower.PartialVerticalMatch upper) (w : {w : Fin B // upper.finish w = none}) :
    j.glue.x (upperCapEquiv j w).val 1 = upper.x w.val 1 := by
  change j.glue.x (j.upperId w.val) 1 = _
  have h := j.glue_x_upper w.val (y := 1) (by norm_num)
  simpa only [show slabHeight 1 1 = 1 by norm_num [slabHeight]] using h

noncomputable def upperJoin : (lowerJoin m).glue.PartialVerticalMatch upper where
  contact := (upperCapEquiv (lowerJoin m)).symm.trans (collarUpperContact m)
  label z := by
    let e := upperCapEquiv (lowerJoin m)
    change (lowerJoin m).glue.label z.val = upper.label (collarUpperContact m (e.symm z)).val
    calc
      _ = (lowerJoin m).glue.label (e (e.symm z)).val := by rw [e.apply_symm_apply]
      _ = (collar m).label (e.symm z).val := upperCap_label (lowerJoin m) _
      _ = _ := collarUpper_label m _
  coordinate z := by
    let e := upperCapEquiv (lowerJoin m)
    change (lowerJoin m).glue.x z.val 1 = upper.x (collarUpperContact m (e.symm z)).val 0
    calc
      _ = (lowerJoin m).glue.x (e (e.symm z)).val 1 := by rw [e.apply_symm_apply]
      _ = (collar m).x (e.symm z).val 1 := upperCap_x (lowerJoin m) _
      _ = _ := collarUpper_x m _

/-- Both original names of a contact feed the same composite wire. -/
theorem glue_matches_contact (w : PartialVerticalMatch.Contact lower) :
    PartialVerticalMatch.lowerId (upper := upper)
      (PartialVerticalMatch.lowerId (upper := collar m) w.val) =
      (upperJoin m).upperId (m.contact w).val := by
  let i := (lowerJoin m).contact w
  let e := upperCapEquiv (lowerJoin m)
  let cap : {z // (collar m).finish z = none} := ⟨i.val, (matchCollar m).drawing_finish i.val⟩
  apply (upperJoin m).lowerId_eq_upperId.mpr
  refine ⟨e cap, ?_, ?_⟩
  · exact ((lowerJoin m).upperId_shared w).trans ((lowerJoin m).lowerId_shared w).symm
  · change (collarUpperContact m (e.symm (e cap))).val = _
    rw [e.symm_apply_apply]
    change (m.contact ((collarIndex lower).symm (collarIndex lower w))).val = _
    rw [Equiv.symm_apply_apply]

theorem glue_x_in_collar (w : PartialVerticalMatch.Contact lower) {y : ℝ}
    (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (upperJoin m).glue.x ((upperJoin m).upperId (m.contact w).val) y =
      interpolate (lower.x w.val 1) (upper.x (m.contact w).val 0) (4 * y - 1) := by
  rw [← glue_matches_contact m w]
  have same : PartialVerticalMatch.lowerId (upper := collar m) w.val =
      (lowerJoin m).upperId (collarIndex lower w) :=
    ((lowerJoin m).lowerId_shared w).trans ((lowerJoin m).upperId_shared w).symm
  have high : (1 / 2 : ℝ) ≤ slabHeight 0 y := by unfold slabHeight; linarith [hy.1]
  rw [same, (upperJoin m).glue_x_lower _ hy.2, (lowerJoin m).glue_x_upper _ high]
  change ((matchCollar m).drawing S).x (collarIndex lower w) (slabHeight 1 (slabHeight 0 y)) = _
  rw [CollarSpec.drawing_x]
  have height : slabHeight 1 (slabHeight 0 y) = 4 * y - 1 := by unfold slabHeight; ring
  simp [matchCollar, height]

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
