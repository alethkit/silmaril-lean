module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Thms
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

/-!
# Sweep readback of vertical gluing

This is a slicing comparison for the sequential juxtaposition in Figure 7
and Lemma 3.4 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5 (p. 9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R W : ℕ}
variable {lower : ProgressiveGraph.Diagram S L W .point}
variable {upper : ProgressiveGraph.Diagram S R W .point}
variable (m : lower.VerticalMatch upper)

theorem levels_glue :
    m.glue.levels = lower.levels.map (halfHeight 0) ++ upper.levels.map (halfHeight 1) :=
  (Proofs.ProgressiveGluing.matchedStack m).levels_glue

noncomputable def lowerSweepCut (i : Fin (lower.levelCount + 1)) :
    Fin (m.glue.levelCount + 1) :=
  (Proofs.ProgressiveGluing.matchedStack m).lowerCut i

noncomputable def upperSweepCut (i : Fin (upper.levelCount + 1)) :
    Fin (m.glue.levelCount + 1) :=
  (Proofs.ProgressiveGluing.matchedStack m).upperCut i

/-- The gap index between the lower and upper level sequences. -/
noncomputable def spliceSweepCut : Fin (m.glue.levelCount + 1) :=
  m.lowerSweepCut (Fin.last lower.levelCount)

theorem upperSweepCut_zero : m.upperSweepCut 0 = m.spliceSweepCut :=
  (Proofs.ProgressiveGluing.matchedStack m).upper_join

theorem spliceSweepCut_in_gap : (1 / 2 : ℝ) ∈ m.glue.levelGap m.spliceSweepCut :=
  (Proofs.ProgressiveGluing.matchedStack m).join_gap

/-- Rescale both cut families, retaining the geometric join in place of the
last lower and first upper cut. -/
noncomputable def spliceSweepCuts (p : lower.LayerCuts) (q : upper.LayerCuts) : m.glue.LayerCuts :=
  (Proofs.ProgressiveGluing.matchedStack m).spliceCuts p q

theorem spliceSweepCuts_join (p : lower.LayerCuts) (q : upper.LayerCuts) :
    (m.spliceSweepCuts p q).height m.spliceSweepCut = 1 / 2 :=
  (Proofs.ProgressiveGluing.matchedStack m).spliceCuts_join p q

theorem spliceSweepCuts_lower (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (lower.levelCount + 1)) (before : i.val < lower.levelCount) :
    (m.spliceSweepCuts p q).height (m.lowerSweepCut i) = halfHeight 0 (p.height i) :=
  (Proofs.ProgressiveGluing.matchedStack m).spliceCuts_lower p q i before

theorem spliceSweepCuts_upper (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (upper.levelCount + 1)) (after : 0 < i.val) :
    (m.spliceSweepCuts p q).height (m.upperSweepCut i) = halfHeight 1 (q.height i) :=
  (Proofs.ProgressiveGluing.matchedStack m).spliceCuts_upper p q i after

/-- The lower event's ordered slots transport with the lower vertex IDs. -/
theorem sweep_slots_lower {h a b c d : ℝ} (below : h < 1)
    (p : lower.LayerSlice h a b) (s : m.glue.LayerSlice (halfHeight 0 h) c d) :
    s.slots = p.slots.map (Sum.map id (Fin.castAdd R)) :=
  Proofs.ProgressiveGluing.slots_lower m rfl below p s

/-- The upper event's ordered slots transport with the upper vertex IDs. -/
theorem sweep_slots_upper {h a b c d : ℝ} (above : 0 < h)
    (q : upper.LayerSlice h a b) (s : m.glue.LayerSlice (halfHeight 1 h) c d) :
    s.slots = q.slots.map (Sum.map id (Fin.natAdd L)) :=
  Proofs.ProgressiveGluing.slots_upper m rfl above q s

variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

/-- The ordered ID list agrees at every lower gap, independent of cut choice. -/
theorem sweep_wires_lower (i : Fin (lower.levelCount + 1)) :
    s.wires (m.lowerSweepCut i) = p.wires i :=
  Proofs.ProgressiveGluing.wires_lower m p s i

theorem sweep_wires_upper (i : Fin (upper.levelCount + 1)) :
    s.wires (m.upperSweepCut i) = q.wires i :=
  Proofs.ProgressiveGluing.wires_upper m q s i

/-- The intermediate frontier of any sweep is the ordered cut at the splice. -/
theorem sweep_ordered_at_join : m.glue.OrderedCut (1 / 2) (s.wires m.spliceSweepCut) := by
  exact (Proofs.ProgressiveGluing.wires_join_lower m lower.layerSweep s).symm ▸
    Proofs.ProgressiveGluing.ordered_join_lower m lower.layerSweep

theorem sweep_first_word : s.word 0 = p.word 0 :=
  Proofs.ProgressiveGluing.first_word m p s

theorem sweep_last_word : s.word (Fin.last m.glue.levelCount) = q.word (Fin.last upper.levelCount) :=
  Proofs.ProgressiveGluing.last_word m q s

include m in
theorem sweep_join_word : q.word 0 = p.word (Fin.last lower.levelCount) :=
  Proofs.ProgressiveGluing.join_word m p q

/-- An independently read glued sheet is the exact concatenation of the
independently read operands, after transport of the typed boundary words.
Each distinct height contributes its whole horizontal row, including ties. -/
theorem sweep_concat :
    s.sheet.reindex (m.sweep_first_word p s) (m.sweep_last_word q s) =
      p.sheet.thenDo (q.sheet.reindex (m.sweep_join_word p q) rfl) :=
  Proofs.ProgressiveGluing.sweep_concat m p q s

/-- Independently serializing the tied layers on either side preserves the
seam class of the concatenation. -/
theorem sweep_serial_concat (pp : p.Schedule) (qp : q.Schedule) (sp : s.Schedule) :
    Sliced.Sheet.SeamEquivalent
      ((s.serialSheet sp).reindex (m.sweep_first_word p s) (m.sweep_last_word q s))
      ((p.serialSheet pp).thenDo ((q.serialSheet qp).reindex (m.sweep_join_word p q) rfl)) := by
  have glued := (s.serial_seam sp).reindex (m.sweep_first_word p s) (m.sweep_last_word q s)
  have operands := (p.serial_seam pp).thenDo ((q.serial_seam qp).reindex (m.sweep_join_word p q) rfl)
  rw [← m.sweep_concat p q s] at operands
  exact .trans _ _ _ glued (.symm _ _ operands)

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.VerticalMatch
