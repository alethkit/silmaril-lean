module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialSweep
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing.Regression

open ProgressiveGraph

private abbrev signature : Signature Bool where
  Edge := Option (Bool ⊕ Bool)
  source
    | some (.inr b) => [b]
    | _ => []
  target
    | some (.inl b) => [b]
    | _ => []

private noncomputable def coordinate (mirror : Bool) (w : Fin 2) : ℝ :=
  if w = 0 then (if mirror then 3 / 4 else 1 / 4) else (if mirror then 1 / 4 else 3 / 4)

private def label (mirror : Bool) (w : Fin 2) : Bool := if w = 0 then mirror else !mirror

private noncomputable def vertexX (mirror : Bool) (v : Fin 3) : ℝ :=
  if v = 0 then coordinate mirror 0
  else if v = 1 then coordinate mirror 1
  else if mirror then 1 / 2 else coordinate mirror 1

private def box (mirror : Bool) (v : Fin 3) : Option (Bool ⊕ Bool) :=
  if v = 0 then some (.inl (label mirror 0))
  else if v = 1 then some (.inr (label mirror 1))
  else if mirror then none else some (.inl (label mirror 1))

private noncomputable def height (v : Fin 3) : ℝ := if v = 2 then 1 / 4 else 1 / 2
private def start (mirror : Bool) (w : Fin 2) : Option (Fin 3) :=
  if w = 0 then some 0 else if mirror then none else some 2
private def finish (w : Fin 2) : Option (Fin 3) := if w = 0 then none else some 1

private noncomputable def strand (mirror : Bool) (w : Fin 2) :
    Wire (endpointHeight height 0 (start mirror w)) (endpointHeight height 1 (finish w)) where
  x _ := coordinate mirror w
  increasing := by fin_cases w <;> cases mirror <;> norm_num [start, finish, height, endpointHeight]
  continuous := continuousOn_const
  polygonal := by
    refine ⟨∅, ?_⟩
    intro a _ b _ _ _ t _
    ring

private theorem separated_coordinates (mirror : Bool) {w z : Fin 2} (different : w ≠ z) :
    coordinate mirror w ≠ coordinate mirror z := by
  fin_cases w <;> fin_cases z <;> cases mirror <;> norm_num [coordinate] at *

/-- The lower unmatched wire goes from vertex 2 to vertex 1. On the
upper side vertex 2 is a scalar and wire 0 goes to the exterior cap.
Vertices 0 and 1 are tied in both operands. -/
private noncomputable def drawing (mirror : Bool) : ProgressiveGraph.Diagram signature 3 2 .point where
  vertexX := vertexX mirror
  vertexHeight := height
  vertex_inside := by
    intro v
    fin_cases v <;> cases mirror <;> norm_num [vertexX, coordinate, height, Set.mem_Ioo]
  vertex_separation := by
    intro v z eq
    change (vertexX mirror v, height v) = (vertexX mirror z, height z) at eq
    fin_cases v <;> fin_cases z <;> cases mirror <;> norm_num [vertexX, coordinate, height] at *
  generator := box mirror
  label := label mirror
  start := start mirror
  finish := finish
  wire := strand mirror
  wire_inside := by
    intro w y _
    fin_cases w <;> cases mirror <;> norm_num [strand, coordinate, Set.mem_Ioo]
  start_attached := by
    intro w v h
    fin_cases w <;> cases mirror <;> simp [start] at h
    all_goals subst v; rfl
  finish_attached := by
    intro w v h
    fin_cases w <;> simp [finish] at h
    subst v
    rfl
  separated := fun ne _ _ _ => separated_coordinates mirror ne
  avoids_vertex := by
    intro w v h
    fin_cases w <;> fin_cases v <;> cases mirror <;>
      norm_num [start, finish, height, endpointHeight, Set.mem_Ioo, strand, vertexX, coordinate] at *
  input_boundary_separated := fun ne _ _ => separated_coordinates mirror ne
  output_boundary_separated := fun ne _ _ => separated_coordinates mirror ne
  input _ _ := 1
  output v _ := if v = 2 then 1 else 0
  input_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> cases mirror <;> simp [signature, finish, box]
  output_exact := by
    intro v w
    fin_cases v <;> fin_cases w <;> cases mirror <;> simp [signature, start, box]
  input_types := by
    intro v
    fin_cases v <;> cases mirror <;> simp [box]
  output_types := by
    intro v
    fin_cases v <;> cases mirror <;> simp [box]
  input_order := by
    intro v i j h
    exfalso
    have hj := j.isLt
    have small : (signature.source (box mirror v)).length ≤ 1 := by
      fin_cases v <;> cases mirror <;> simp [box]
    omega
  output_order := by
    intro v i j h
    exfalso
    have hj := j.isLt
    have small : (signature.target (box mirror v)).length ≤ 1 := by
      fin_cases v <;> cases mirror <;> simp [box]
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
  change start true w = none at h
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

example : matched.glue.inputs (Fin.castAdd 3 1) = [Diagram.PartialVerticalMatch.lowerId 1] := by
  rw [matched.glue_inputs_lower]
  rfl

example : matched.glue.outputs (Fin.natAdd 3 0) = [matched.upperId 0] := by
  rw [matched.glue_outputs_upper]
  rfl

/-- The lower-only strand remains active before its original sink. -/
example : matched.glue.OrderedCut (halfHeight 0 (3 / 8)) [Diagram.PartialVerticalMatch.lowerId 1] := by
  refine matched.cut_lower (ws := [1]) (by norm_num) ⟨?_, List.pairwise_singleton _ _⟩
  intro w
  change w ∈ [1] ↔ endpointHeight height 0 (start false w) < 3 / 8 ∧
    (3 / 8 : ℝ) < endpointHeight height 1 (finish w)
  fin_cases w <;> norm_num [start, finish, endpointHeight, height]

/-- The upper-only strand remains active after its original source. -/
example : matched.glue.OrderedCut (halfHeight 1 (3 / 4)) [matched.upperId 0] := by
  refine matched.cut_upper (ws := [0]) (by norm_num) ⟨?_, List.pairwise_singleton _ _⟩
  intro w
  change w ∈ [0] ↔ endpointHeight height 0 (start true w) < 3 / 4 ∧
    (3 / 4 : ℝ) < endpointHeight height 1 (finish w)
  fin_cases w <;> norm_num [start, finish, endpointHeight, height]

private theorem operand_levels (mirror : Bool) :
    (drawing mirror).levels = [1 / 4, 1 / 2] := by
  have image : Finset.univ.image (drawing mirror).vertexHeight = ({1 / 4, 1 / 2} : Finset ℝ) := by
    ext h
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      fin_cases v <;> norm_num [drawing, height]
    · rintro (rfl | rfl)
      · exact ⟨2, by norm_num [drawing, height]⟩
      · exact ⟨0, by norm_num [drawing, height]⟩
  rw [Diagram.levels, image, Finset.sort_insert (· ≤ ·) (by intro b hb; simp at hb; rw [hb]; norm_num)
    (by norm_num), Finset.sort_singleton]

example : matched.glue.levels = [1 / 8, 1 / 4, 5 / 8, 3 / 4] := by
  rw [matched.levels_glue]
  change (drawing false).levels.map (halfHeight 0) ++ (drawing true).levels.map (halfHeight 1) = _
  rw [operand_levels, operand_levels]
  norm_num [halfHeight]

private noncomputable def lowerRead := lower.layerSweep
private noncomputable def upperRead := upper.layerSweep
private noncomputable def gluedRead := matched.glue.layerSweep

private noncomputable def atSplice := matched.glue.layerSweepAt
  (matched.spliceSweepCuts lowerRead.cuts upperRead.cuts)

example : atSplice.cuts.height matched.spliceSweepCut = 1 / 2 := by
  unfold atSplice
  rw [Diagram.layerSweepAt_cuts, matched.spliceSweepCuts_join]

example : atSplice.wires matched.spliceSweepCut = [matched.sharedId shared] :=
  Diagram.ordered_cut_unique (matched.sweep_ordered_at_join atSplice)
    (matched.ordered_join (fun w => List.mem_singleton.mpr (Subtype.ext (lower_contact w)))
      (List.pairwise_singleton _ _))

/-- The unmatched internal wire still reaches its lower sink in the sweep. -/
example : Diagram.PartialVerticalMatch.lowerId 1 ∈
    (atSplice.layer (matched.lowerSweepLevel (lower.levelIndex 1))).slots.flatMap matched.glue.slotInputs := by
  apply List.mem_flatMap.mpr
  refine ⟨.inr (Fin.castAdd 3 1), ?_, ?_⟩
  · rw [matched.sweep_slots_lower lowerRead, List.mem_map]
    exact ⟨.inr 1, ((lowerRead.layer _).exact_slots (.inr 1)).mpr (lower.levelHeight_index 1).symm, rfl⟩
  · change Diagram.PartialVerticalMatch.lowerId 1 ∈ matched.glue.inputs (Fin.castAdd 3 1)
    rw [matched.glue_inputs_lower]
    exact List.mem_singleton_self _

example (i : Fin upper.levelCount) : Diagram.PartialVerticalMatch.lowerId 1 ∉
    ((gluedRead.layer (matched.upperSweepLevel i)).slots.flatMap matched.glue.slotInputs) ++
      ((gluedRead.layer (matched.upperSweepLevel i)).slots.flatMap matched.glue.slotOutputs) :=
  matched.sweep_lower_only_not_in_upper gluedRead 1 (by decide) i

/-- The independently sliced composite has four levels with one tie per
side. Its exact typed sheet is the concatenation of the operand reads. -/
example :
    gluedRead.sheet.reindex (matched.sweep_first_word lowerRead gluedRead) (matched.sweep_last_word upperRead gluedRead) =
      lowerRead.sheet.thenDo (upperRead.sheet.reindex (matched.sweep_join_word lowerRead upperRead) rfl) :=
  matched.sweep_concat lowerRead upperRead gluedRead

private noncomputable def reverseSchedule {V W : ℕ} {d : ProgressiveGraph.Diagram signature V W .point}
    (s : d.LayerSweep) : s.Schedule :=
  ⟨fun i => (s.layer i).vertices.reverse, fun i => List.reverse_perm (s.layer i).vertices⟩

example :
    Sliced.Sheet.SeamEquivalent
      ((gluedRead.serialSheet (reverseSchedule gluedRead)).reindex
        (matched.sweep_first_word lowerRead gluedRead) (matched.sweep_last_word upperRead gluedRead))
      ((lowerRead.serialSheet (reverseSchedule lowerRead)).thenDo
        ((upperRead.serialSheet (reverseSchedule upperRead)).reindex (matched.sweep_join_word lowerRead upperRead) rfl)) :=
  matched.sweep_serial_concat lowerRead upperRead gluedRead
    (reverseSchedule lowerRead) (reverseSchedule upperRead) (reverseSchedule gluedRead)

end Silmaril.RuntimeWires.Proofs.PartialGluing.Regression
