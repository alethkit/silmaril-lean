module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarMotion
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarJoins
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialAssembly
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram PartialVerticalMatch
open Proofs.PartialGluing
open OrderedVerticalMatch (collarIndex collarCount)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

noncomputable def straightChoice : PolygonalCollar m.collarSpec where
  wire := collarWire m.collarSpec
  bottom _ := interpolate_at_zero _ _
  top _ := interpolate_at_one _ _
  inside w _ hy := interpolate_inside (m.collarSpec.bottom_inside w) (m.collarSpec.top_inside w) hy
  ordered a b _ hy order := (collar_order m.collarSpec (a := a) (b := b) hy).mpr order

variable (p : PolygonalCollar m.collarSpec)

noncomputable def lowerChoice : lower.PartialVerticalMatch (polygonalDrawing (S := S) p) where
  contact := (collarIndex lower).trans (allCap fun _ => rfl)
  label w := by
    change lower.label w.val = m.collarSpec.label (collarIndex lower w)
    rw [m.collarSpec_label, Equiv.symm_apply_apply]
  coordinate w := by
    change lower.x w.val 1 = (p.wire (collarIndex lower w)).x 0
    rw [p.bottom, m.collarSpec_bottom, Equiv.symm_apply_apply]

noncomputable def lowerAttached := assemble (lowerChoice m p)

/-- The top contacts of the first attachment, with their original collar IDs. -/
noncomputable def collarOutputEquiv : Fin (collarCount lower) ≃
    {z // (lowerAttached m p).finish z = none} :=
  Equiv.ofBijective
    (fun w => ⟨(lowerChoice m p).upperId w, by
      show (assemble (lowerChoice m p)).finish _ = none
      rw [finish_upper_id]
      rfl⟩)
    ⟨fun _ _ eq => fromUpper_injective (lowerChoice m p)
        ((numbering lower (polygonalDrawing p)).injective (congrArg Subtype.val eq)),
      fun z => by
        have hz : (assemble (lowerChoice m p)).finish z.val = none := z.property
        obtain ⟨w, _, eq⟩ := finish_cap_exists (lowerChoice m p) hz
        exact ⟨w, Subtype.ext eq⟩⟩

theorem collarOutput_x (i : Fin (collarCount lower)) :
    (lowerAttached m p).x (collarOutputEquiv m p i).val 1 = (p.wire i).x 1 := by
  let j := lowerChoice m p
  let e := numbering lower (polygonalDrawing p)
  change jointX j (e.symm (e (j.fromUpper i))) 1 = _
  rw [e.symm_apply_apply]
  have atTop := x_fromUpper j i (y := 1) (by norm_num)
  change jointX j (j.fromUpper i) 1 = _
  change jointX j (j.fromUpper i) 1 = (p.wire i).x (slabHeight 1 1) at atTop
  rwa [show slabHeight 1 1 = 1 by norm_num [slabHeight]] at atTop

theorem collarOutput_label (i : Fin (collarCount lower)) :
    (lowerAttached m p).label (collarOutputEquiv m p i).val = m.collarSpec.label i := by
  let j := lowerChoice m p
  let e := numbering lower (polygonalDrawing p)
  change wireLabel (e.symm (e (j.fromUpper i))) = _
  rw [e.symm_apply_apply]
  exact label_fromUpper j i

noncomputable def upperChoice : (lowerAttached m p).PartialVerticalMatch upper where
  contact := (collarOutputEquiv m p).symm.trans ((collarIndex lower).symm.trans m.contact)
  label z := by
    let e := collarOutputEquiv m p
    change (lowerAttached m p).label z.val =
      upper.label (m.contact ((collarIndex lower).symm (e.symm z))).val
    calc
      _ = (lowerAttached m p).label (e (e.symm z)).val := by rw [e.apply_symm_apply]
      _ = m.collarSpec.label (e.symm z) := collarOutput_label m p _
      _ = _ := (m.collarSpec_label _).trans (m.label _)
  coordinate z := by
    let e := collarOutputEquiv m p
    change (lowerAttached m p).x z.val 1 =
      upper.x (m.contact ((collarIndex lower).symm (e.symm z))).val 0
    calc
      _ = (lowerAttached m p).x (e (e.symm z)).val 1 := by rw [e.apply_symm_apply]
      _ = (p.wire (e.symm z)).x 1 := collarOutput_x m p _
      _ = _ := (p.top _).trans (m.collarSpec_top _)

noncomputable def choiceWireCount : ℕ :=
  wireCount (lowerAttached m (straightChoice m)) upper

noncomputable def glueChoice : ProgressiveGraph.Diagram S (L + R) (choiceWireCount m) .point := by
  exact assemble (lower := lowerAttached m p) (upper := upper) (upperChoice m p)

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
