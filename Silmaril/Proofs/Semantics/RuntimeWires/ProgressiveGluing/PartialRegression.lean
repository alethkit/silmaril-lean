module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing.Regression

open ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Bool ⊕ Bool
  source := Sum.elim (fun _ => []) (fun b => [b])
  target := Sum.elim (fun b => [b]) (fun _ => [])

private noncomputable def coordinate (mirror : Bool) (w : Fin 2) : ℝ :=
  if w = 0 then (if mirror then 3 / 4 else 1 / 4) else (if mirror then 1 / 4 else 3 / 4)

private def label (mirror : Bool) (w : Fin 2) : Bool := if w = 0 then mirror else !mirror
private def box (mirror : Bool) (v : Fin 2) : Bool ⊕ Bool :=
  if v = 0 then .inl (label mirror v) else .inr (label mirror v)

private noncomputable def height (_ : Fin 2) : ℝ := 1 / 2
private def start (w : Fin 2) : Option (Fin 2) := if w = 0 then some 0 else none
private def finish (w : Fin 2) : Option (Fin 2) := if w = 0 then none else some 1

private noncomputable def strand (mirror : Bool) (w : Fin 2) :
    Wire (endpointHeight height 0 (start w)) (endpointHeight height 1 (finish w)) where
  x _ := coordinate mirror w
  increasing := by fin_cases w <;> norm_num [start, finish, height, endpointHeight]
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

private theorem separated_coordinates (mirror : Bool) {w z : Fin 2} (different : w ≠ z) :
    coordinate mirror w ≠ coordinate mirror z := by
  fin_cases w <;> fin_cases z <;> cases mirror <;> norm_num [coordinate] at *

/-- Each operand has one source-to-cap wire and one cap-to-sink wire.
Mirroring the upper drawing assigns the common cap contact different IDs. -/
private noncomputable def drawing (mirror : Bool) : Diagram signature 2 2 .point where
  vertexX := coordinate mirror
  vertexHeight := height
  vertex_inside := by
    intro v
    fin_cases v <;> cases mirror <;> norm_num [coordinate, height, Set.mem_Ioo]
  vertex_separation := by
    intro v z eq
    by_contra h
    exact separated_coordinates mirror h (congrArg Prod.fst eq)
  generator := box mirror
  label := label mirror
  start := start
  finish := finish
  wire := strand mirror
  wire_inside := by
    intro w y _
    fin_cases w <;> cases mirror <;> norm_num [strand, coordinate, Set.mem_Ioo]
  start_attached := by
    intro w v h
    fin_cases w <;> simp [start] at h
    subst v
    rfl
  finish_attached := by
    intro w v h
    fin_cases w <;> simp [finish] at h
    subst v
    rfl
  separated := fun ne _ _ _ => separated_coordinates mirror ne
  avoids_vertex := by
    intro w v h
    fin_cases w <;> norm_num [start, finish, height, endpointHeight, Set.mem_Ioo] at h
  input_boundary_separated := fun ne _ _ => separated_coordinates mirror ne
  output_boundary_separated := fun ne _ _ => separated_coordinates mirror ne
  input _ _ := 1
  output _ _ := 0
  input_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, finish, box]
  output_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> simp [signature, start, box]
  input_types := by
    intro v
    fin_cases v <;> simp [box]
  output_types := by
    intro v
    fin_cases v <;> simp [box]
  input_order := by
    intro v i j h
    exfalso
    have hj := j.isLt
    have small : (signature.source (box mirror v)).length ≤ 1 := by
      fin_cases v <;> simp [box]
    omega
  output_order := by
    intro v i j h
    exfalso
    have hj := j.isLt
    have small : (signature.target (box mirror v)).length ≤ 1 := by
      fin_cases v <;> simp [box]
    omega

private noncomputable def lower := drawing false
private noncomputable def upper := drawing true

private theorem lower_contact (w : Diagram.PartialVerticalMatch.Contact lower) : w.val = 0 := by
  obtain ⟨w, h⟩ := w
  change finish w = none at h
  by_contra ne
  simp [finish, ne] at h

private theorem upper_contact (w : {w : Fin 2 // upper.start w = none}) : w.val = 1 := by
  obtain ⟨w, h⟩ := w
  change start w = none at h
  have ne : w ≠ 0 := by
    intro eq
    subst w
    cases h
  fin_cases w
  · exact (ne rfl).elim
  · rfl

private noncomputable def matched : lower.PartialVerticalMatch upper where
  contact :=
    { toFun := fun _ => ⟨1, rfl⟩
      invFun := fun _ => ⟨0, rfl⟩
      left_inv := fun w => Subtype.ext (lower_contact w).symm
      right_inv := fun w => Subtype.ext (upper_contact w).symm }
  label w := by
    change lower.label w.val = upper.label 1
    rw [lower_contact w]
    rfl
  coordinate w := by
    change lower.x w.val 1 = upper.x 1 0
    rw [lower_contact w]
    rfl

private def shared : Diagram.PartialVerticalMatch.Contact lower := ⟨0, rfl⟩

example : Diagram.PartialVerticalMatch.lowerId 0 = matched.upperId 1 :=
  matched.lowerId_eq_upperId.mpr ⟨shared, rfl, rfl⟩

example : Diagram.PartialVerticalMatch.lowerId 1 ≠ matched.upperId 0 := by
  intro h
  obtain ⟨w, hw, _⟩ := matched.lowerId_eq_upperId.mp h
  have bad := (lower_contact w).symm.trans hw
  exact (by decide : (0 : Fin 2) ≠ 1) bad

example : matched.glue.OrderedCut (1 / 2) [matched.sharedId shared] :=
  matched.ordered_join (fun w => List.mem_singleton.mpr (Subtype.ext (lower_contact w)))
    (List.pairwise_singleton _ _)

example : matched.glue.inputs (Fin.castAdd 2 1) = [Diagram.PartialVerticalMatch.lowerId 1] := by
  rw [matched.glue_inputs_lower]
  rfl

example : matched.glue.outputs (Fin.natAdd 2 0) = [matched.upperId 0] := by
  rw [matched.glue_outputs_upper]
  rfl

/-- The lower-only strand remains active before its original sink. -/
example : matched.glue.OrderedCut (halfHeight 0 (1 / 4)) [Diagram.PartialVerticalMatch.lowerId 1] := by
  refine matched.cut_lower (ws := [1]) (by norm_num) ⟨?_, List.pairwise_singleton _ _⟩
  intro w
  change w ∈ [1] ↔ endpointHeight height 0 (start w) < 1 / 4 ∧
    (1 / 4 : ℝ) < endpointHeight height 1 (finish w)
  fin_cases w <;> norm_num [start, finish, endpointHeight, height]

/-- The upper-only strand remains active after its original source. -/
example : matched.glue.OrderedCut (halfHeight 1 (3 / 4)) [matched.upperId 0] := by
  refine matched.cut_upper (ws := [0]) (by norm_num) ⟨?_, List.pairwise_singleton _ _⟩
  intro w
  change w ∈ [0] ↔ endpointHeight height 0 (start w) < 3 / 4 ∧
    (3 / 4 : ℝ) < endpointHeight height 1 (finish w)
  fin_cases w <;> norm_num [start, finish, endpointHeight, height]

end Silmaril.RuntimeWires.Proofs.PartialGluing.Regression
