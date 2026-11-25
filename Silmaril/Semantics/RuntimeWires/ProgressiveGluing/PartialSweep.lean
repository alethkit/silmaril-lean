module

public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.Partial
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
public import Silmaril.Semantics.RuntimeWires.TiedHeightSweep.Thms
import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialSweepReadback

public section

/-!
# Sweep readback for typed cap gluing

A slicing comparison for the sequential juxtaposition in Figure 7 and
Lemma 3.4 of Mario Román and Paweł Sobociński,
*String Diagrams for Premonoidal Categories*, arXiv:2305.06075v5 (p. 9:7).

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.ProgressiveGraph.Diagram.PartialVerticalMatch

open Proofs.PartialGluing

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point}
variable {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)

theorem levels_glue :
    m.glue.levels = lower.levels.map (halfHeight 0) ++ upper.levels.map (halfHeight 1) :=
  (sweepStack m).levels_glue

noncomputable def lowerSweepLevel (i : Fin lower.levelCount) : Fin m.glue.levelCount :=
  (sweepStack m).lowerLevel i

noncomputable def upperSweepLevel (i : Fin upper.levelCount) : Fin m.glue.levelCount :=
  (sweepStack m).upperLevel i

noncomputable def lowerSweepCut (i : Fin (lower.levelCount + 1)) : Fin (m.glue.levelCount + 1) :=
  (sweepStack m).lowerCut i

noncomputable def upperSweepCut (i : Fin (upper.levelCount + 1)) : Fin (m.glue.levelCount + 1) :=
  (sweepStack m).upperCut i

/-- The gap between the last lower level and first upper level. -/
noncomputable def spliceSweepCut : Fin (m.glue.levelCount + 1) :=
  (sweepStack m).joinCut

theorem spliceSweepCut_in_gap : (1 / 2 : ℝ) ∈ m.glue.levelGap m.spliceSweepCut :=
  (sweepStack m).join_gap

/-- Use the rescaled cuts from each slab and read their shared boundary at
the geometric splice itself. -/
noncomputable def spliceSweepCuts (p : lower.LayerCuts) (q : upper.LayerCuts) : m.glue.LayerCuts :=
  (sweepStack m).spliceCuts p q

theorem spliceSweepCuts_join (p : lower.LayerCuts) (q : upper.LayerCuts) :
    (m.spliceSweepCuts p q).height m.spliceSweepCut = 1 / 2 :=
  (sweepStack m).spliceCuts_join p q

theorem spliceSweepCuts_lower (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (lower.levelCount + 1)) (before : i.val < lower.levelCount) :
    (m.spliceSweepCuts p q).height (m.lowerSweepCut i) = halfHeight 0 (p.height i) :=
  (sweepStack m).spliceCuts_lower p q i before

theorem spliceSweepCuts_upper (p : lower.LayerCuts) (q : upper.LayerCuts)
    (i : Fin (upper.levelCount + 1)) (after : 0 < i.val) :
    (m.spliceSweepCuts p q).height (m.upperSweepCut i) = halfHeight 1 (q.height i) :=
  (sweepStack m).spliceCuts_upper p q i after

variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem sweep_wires_lower (i : Fin (lower.levelCount + 1)) :
    s.wires (m.lowerSweepCut i) = (p.wires i).map lowerId :=
  wires_lower m p s i

theorem sweep_wires_upper (i : Fin (upper.levelCount + 1)) :
    s.wires (m.upperSweepCut i) = (q.wires i).map m.upperId :=
  wires_upper m q s i

theorem sweep_wires_join_lower :
    s.wires m.spliceSweepCut = (p.wires (Fin.last lower.levelCount)).map lowerId :=
  wires_join_lower m p s

theorem sweep_wires_join_upper :
    s.wires m.spliceSweepCut = (q.wires 0).map m.upperId :=
  wires_join_upper m q s

theorem sweep_ordered_at_join : m.glue.OrderedCut (1 / 2) (s.wires m.spliceSweepCut) :=
  ordered_at_join m s

/-- Exactly the same ordered slots, under the lower wire and vertex embeddings. -/
theorem sweep_slots_lower (i : Fin lower.levelCount) :
    (s.layer (m.lowerSweepLevel i)).slots = (p.layer i).slots.map (Sum.map lowerId (Fin.castAdd R)) :=
  slots_lower m ((sweepStack m).height_lower i)
    ((p.layer i).isolation.above.trans (p.layer i).isolation.hi_inside) (p.layer i) _

/-- Exactly the same ordered slots, under the upper wire and vertex embeddings. -/
theorem sweep_slots_upper (i : Fin upper.levelCount) :
    (s.layer (m.upperSweepLevel i)).slots = (q.layer i).slots.map (Sum.map m.upperId (Fin.natAdd L)) :=
  slots_upper m ((sweepStack m).height_upper i)
    ((q.layer i).isolation.lo_inside.trans (q.layer i).isolation.below) (q.layer i) _

/-- A lower-only strand is absent from both frontiers of every upper row. -/
theorem sweep_lower_only_not_in_upper (w : Fin A) (notAtCap : lower.finish w ≠ none)
    (i : Fin upper.levelCount) :
    lowerId w ∉ ((s.layer (m.upperSweepLevel i)).slots.flatMap m.glue.slotInputs) ++
      ((s.layer (m.upperSweepLevel i)).slots.flatMap m.glue.slotOutputs) :=
  lower_only_not_in_upper m s w notAtCap i

/-- An upper-only strand is absent from both frontiers of every lower row. -/
theorem sweep_upper_only_not_in_lower (w : Fin B) (notAtCap : upper.start w ≠ none)
    (i : Fin lower.levelCount) :
    m.upperId w ∉ ((s.layer (m.lowerSweepLevel i)).slots.flatMap m.glue.slotInputs) ++
      ((s.layer (m.lowerSweepLevel i)).slots.flatMap m.glue.slotOutputs) :=
  upper_only_not_in_lower m s w notAtCap i

theorem sweep_first_word : s.word 0 = p.word 0 :=
  first_word m p s

theorem sweep_last_word : s.word (Fin.last m.glue.levelCount) = q.word (Fin.last upper.levelCount) :=
  last_word m q s

include m in
theorem sweep_join_word : q.word 0 = p.word (Fin.last lower.levelCount) :=
  join_word m p q

/-- The independently read glued and operand sheets agree by exact typed
concatenation, for arbitrary valid cuts, including all tied levels. -/
theorem sweep_concat :
    s.sheet.reindex (m.sweep_first_word p s) (m.sweep_last_word q s) =
      p.sheet.thenDo (q.sheet.reindex (m.sweep_join_word p q) rfl) :=
  Proofs.PartialGluing.sweep_concat m p q s

/-- Independently serializing each level preserves this comparison up to
the existing typed seam equivalence. -/
theorem sweep_serial_concat (pp : p.Schedule) (qp : q.Schedule) (sp : s.Schedule) :
    Sliced.Sheet.SeamEquivalent
      ((s.serialSheet sp).reindex (m.sweep_first_word p s) (m.sweep_last_word q s))
      ((p.serialSheet pp).thenDo ((q.serialSheet qp).reindex (m.sweep_join_word p q) rfl)) :=
  Proofs.PartialGluing.sweep_serial_concat m p q s pp qp sp

end Silmaril.RuntimeWires.ProgressiveGraph.Diagram.PartialVerticalMatch
