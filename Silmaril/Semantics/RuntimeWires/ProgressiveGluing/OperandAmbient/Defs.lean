module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Collar
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Tactic.Ring

@[expose] public section

namespace Silmaril.RuntimeWires.ProgressiveGraph

/-- A genuine ambient isotopy, supported in the open unit-height slab. -/
structure SlabIsotopy where
  frame : Set.Icc (0 : ℝ) 1 → (ℝ × ℝ) ≃ₜ (ℝ × ℝ)
  zero : ∀ z, frame ⟨0, le_rfl, zero_le_one⟩ z = z
  continuous_frame : Continuous (fun z : Set.Icc (0 : ℝ) 1 × (ℝ × ℝ) => frame z.1 z.2)
  continuous_inverse : Continuous (fun z : Set.Icc (0 : ℝ) 1 × (ℝ × ℝ) => (frame z.1).symm z.2)
  height : ∀ t z, (frame t z).2 = z.2
  outside : ∀ t z, z.2 ≤ 0 ∨ 1 ≤ z.2 → frame t z = z

namespace SlabIsotopy

abbrev Time := Set.Icc (0 : ℝ) 1

/-- Placement of a normalized operand in one of the two half-height slabs. -/
noncomputable def place (offset : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun z := (z.1, halfHeight offset z.2)
  invFun z := (z.1, slabHeight offset z.2)
  left_inv := by intro z; exact Prod.ext rfl (by unfold slabHeight halfHeight; ring)
  right_inv := by intro z; exact Prod.ext rfl (by unfold slabHeight halfHeight; ring)
  continuous_toFun := continuous_fst.prodMk ((continuous_snd.add continuous_const).div_const 2)
  continuous_invFun := continuous_fst.prodMk ((continuous_snd.const_mul 2).sub continuous_const)

/-- A placed map is defined on the whole plane, including the slab caps. -/
noncomputable def placed (f : SlabIsotopy) (offset : ℝ) (t : Time) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (place offset).symm.trans ((f.frame t).trans (place offset))

end SlabIsotopy

namespace Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {V A B : ℕ}

/-- Correspondence of independently valid polygonal drawings at one
time. A wire equivalence accounts for numbering at splices. -/
structure AmbientFrame (d : Diagram S V A .point) (e : Diagram S V B .point)
    (f : (ℝ × ℝ) ≃ₜ (ℝ × ℝ)) where
  rename : Fin A ≃ Fin B
  heights : e.vertexHeight = d.vertexHeight
  generators : e.generator = d.generator
  label : ∀ w, e.label (rename w) = d.label w
  start : ∀ w, e.start (rename w) = d.start w
  finish : ∀ w, e.finish (rename w) = d.finish w
  inputs : ∀ j, e.inputs j = (d.inputs j).map rename
  outputs : ∀ j, e.outputs j = (d.outputs j).map rename
  wire : ∀ w y, d.covers w y → f (d.x w y, y) = (e.x (rename w) y, y)
  vertex : ∀ j, f (d.vertexX j, d.vertexHeight j) = (e.vertexX j, e.vertexHeight j)

/-- A supported ambient isotopy through valid finite polygonal frames. -/
structure AmbientMotion (d : Diagram S V A .point) where
  isotopy : SlabIsotopy
  wireCount : SlabIsotopy.Time → ℕ
  drawing : ∀ t, Diagram S V (wireCount t) .point
  correspondence : ∀ t, AmbientFrame d (drawing t) (isotopy.frame t)

end Diagram
end Silmaril.RuntimeWires.ProgressiveGraph
