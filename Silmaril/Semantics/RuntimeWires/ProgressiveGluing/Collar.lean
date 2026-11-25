module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.CollarGeometry
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialSweep
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarSweep

public section

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

/-- The vertex-free interpolation between the two matched caps. -/
noncomputable def collar : ProgressiveGraph.Diagram S 0 (collarCount lower) .point :=
  Proofs.ProgressiveGluing.collar m

theorem collar_x (w : PartialVerticalMatch.Contact lower) (y : ℝ) :
    m.collar.x (collarIndex lower w) y = interpolate (lower.x w.val 1) (upper.x (m.contact w).val 0) y := by
  rw [show m.collar = (Proofs.ProgressiveGluing.matchCollar m).drawing S from rfl, CollarSpec.drawing_x]
  simp [Proofs.ProgressiveGluing.matchCollar]

theorem collar_label (w : PartialVerticalMatch.Contact lower) :
    m.collar.label (collarIndex lower w) = lower.label w.val := by
  rw [show m.collar = (Proofs.ProgressiveGluing.matchCollar m).drawing S from rfl, CollarSpec.drawing_label]
  simp [Proofs.ProgressiveGluing.matchCollar]

theorem collar_ordered (a b : PartialVerticalMatch.Contact lower) {y : ℝ} (hy : y ∈ Set.Icc 0 1) :
    m.collar.x (collarIndex lower a) y < m.collar.x (collarIndex lower b) y ↔ lower.x a.val 1 < lower.x b.val 1 := by
  rw [show m.collar = (Proofs.ProgressiveGluing.matchCollar m).drawing S from rfl, CollarSpec.drawing_order _ _ _ hy]
  simp [Proofs.ProgressiveGluing.matchCollar]

theorem collar_crosses (w : Fin (collarCount lower)) {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
    m.collar.crosses w y :=
  (Proofs.ProgressiveGluing.matchCollar m).drawing_crosses w hy

theorem collar_ordered_cut {ws : List (PartialVerticalMatch.Contact lower)} (all : ∀ w, w ∈ ws)
    (ordered : ws.Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1))
    {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
    m.collar.OrderedCut y (ws.map (collarIndex lower)) :=
  Proofs.ProgressiveGluing.collar_ordered_cut m all ordered hy

theorem collar_word (s : m.collar.LayerSweep) : s.word (Fin.last m.collar.levelCount) = s.word 0 :=
  Proofs.ProgressiveGluing.vertex_free_word s

/-- At every admissible cut the collar reads the identity with the
ordered labels of its boundary contacts. -/
theorem collar_identity (s : m.collar.LayerSweep) :
    s.sheet.reindex rfl (m.collar_word s) = Sliced.Sheet.empty (s.word 0) :=
  Proofs.ProgressiveGluing.vertex_free_identity s

noncomputable def lowerJoin : lower.PartialVerticalMatch m.collar :=
  Proofs.ProgressiveGluing.lowerJoin m

noncomputable def upperJoin : m.lowerJoin.glue.PartialVerticalMatch upper :=
  Proofs.ProgressiveGluing.upperJoin m

/-- Composition by two half-height gluings. The collar occupies the slab
between heights `1/4` and `1/2`. -/
noncomputable def glue :
    ProgressiveGraph.Diagram S (L + R) (PartialVerticalMatch.wireCount m.lowerJoin.glue upper) .point :=
  Proofs.ProgressiveGluing.glueCollar m

theorem glue_eq_upperJoin : m.glue = m.upperJoin.glue := by rfl

/-- Renaming through both splices identifies the two original contact IDs. -/
theorem glue_matches_contact (w : PartialVerticalMatch.Contact lower) :
    PartialVerticalMatch.lowerId (upper := upper)
      (PartialVerticalMatch.lowerId (upper := m.collar) w.val) =
      m.upperJoin.upperId (m.contact w).val :=
  Proofs.ProgressiveGluing.glue_matches_contact m w

/-- In the composite collar slab, the common wire follows the same
interpolation at its rescaled height. -/
theorem glue_x_in_collar (w : PartialVerticalMatch.Contact lower) {y : ℝ}
    (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    m.glue.x (m.upperJoin.upperId (m.contact w).val) y =
      interpolate (lower.x w.val 1) (upper.x (m.contact w).val 0) (4 * y - 1) :=
  Proofs.ProgressiveGluing.glue_x_in_collar m w hy

/-- The whole collar slab, including both joins, is free of events. -/
theorem collar_band_regular {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    m.glue.Regular y :=
  Proofs.ProgressiveGluing.collar_band_regular m hy

variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem sweep_first_word : s.word 0 = p.word 0 :=
  Proofs.ProgressiveGluing.collar_first_word m p s

theorem sweep_last_word :
    s.word (Fin.last m.glue.levelCount) = q.word (Fin.last upper.levelCount) :=
  Proofs.ProgressiveGluing.collar_last_word m q s

include m in
theorem sweep_join_word : q.word 0 = p.word (Fin.last lower.levelCount) :=
  Proofs.ProgressiveGluing.collar_join_word m p q

/-- Independent sweeps of the operands and the collared composite agree by
exact typed concatenation. The vertex-free collar contributes no rows. -/
theorem sweep_concat :
    s.sheet.reindex (m.sweep_first_word p s) (m.sweep_last_word q s) =
      p.sheet.thenDo (q.sheet.reindex (m.sweep_join_word p q) rfl) :=
  Proofs.ProgressiveGluing.collar_concat m p q s

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.OrderedVerticalMatch
