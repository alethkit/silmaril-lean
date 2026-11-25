module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.CollarJoins
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback
public import Silmaril.Semantics.RuntimeWires.ProgressiveGluing.PartialSweep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Sheet)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B W : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.OrderedVerticalMatch upper)

private theorem vertex_free_count (d : ProgressiveGraph.Diagram S 0 W .point) :
    d.levelCount = 0 := by
  simp [ProgressiveGraph.Diagram.levelCount, ProgressiveGraph.Diagram.levels]

theorem vertex_free_word {d : ProgressiveGraph.Diagram S 0 W .point} (s : d.LayerSweep) :
    s.word (Fin.last d.levelCount) = s.word 0 :=
  congrArg s.word (Fin.ext (vertex_free_count d))

theorem vertex_free_cells {d : ProgressiveGraph.Diagram S 0 W .point} (s : d.LayerSweep) :
    s.sheet.cells = [] := by
  rw [LayerSweep.sheet, cells_joinRows, List.ofFn_eq_nil_iff]
  exact vertex_free_count d

theorem vertex_free_identity {d : ProgressiveGraph.Diagram S 0 W .point} (s : d.LayerSweep) :
    s.sheet.reindex rfl (vertex_free_word s) = Sheet.empty (s.word 0) := by
  apply Sheet.cells_injective
  simpa only [Sheet.cells_reindex, Sheet.cells_empty] using vertex_free_cells s

/-- The ordered lower contacts give an exact ordered cut at every
interior height of the collar. -/
theorem collar_ordered_cut {ws : List (PartialVerticalMatch.Contact lower)}
    (all : ∀ w, w ∈ ws)
    (ordered : ws.Pairwise (fun a b => lower.x a.val 1 < lower.x b.val 1))
    {y : ℝ} (hy : y ∈ Set.Ioo 0 1) :
    (collar m).OrderedCut y (ws.map (OrderedVerticalMatch.collarIndex lower)) := by
  refine ⟨fun i => ⟨fun _ => (matchCollar m).drawing_crosses i hy, fun _ => ?_⟩, ?_⟩
  · exact List.mem_map.mpr ⟨_, all _, Equiv.apply_symm_apply _ _⟩
  · apply List.pairwise_map.mpr
    apply ordered.imp
    intro a b lt
    exact ((matchCollar m).drawing_order _ _ (Set.Ioo_subset_Icc_self hy)).mpr
      (by simpa [matchCollar] using lt)

/-- Gluing the lower operand to the collar and then attaching the upper
operand puts the collar between heights 1/4 and 1/2. -/
noncomputable def glueCollar :
    ProgressiveGraph.Diagram S (L + R) (PartialVerticalMatch.wireCount (lowerJoin m).glue upper) .point :=
  (upperJoin m).glue

theorem collar_band_regular {y : ℝ} (hy : y ∈ Set.Icc (1 / 4 : ℝ) (1 / 2)) :
    (glueCollar m).Regular y := by
  refine ⟨⟨(by norm_num : (0 : ℝ) < 1 / 4).trans_le hy.1,
    hy.2.trans_lt (by norm_num)⟩, ?_⟩
  intro j
  change (upperJoin m).glue.vertexHeight j ≠ y
  induction j using Fin.addCases with
  | left v =>
    have inner : (lowerJoin m).glue.vertexHeight v = halfHeight 0 (lower.vertexHeight v) := by
      have eq : Fin.castAdd 0 v = v := Fin.ext rfl
      simpa only [eq] using (lowerJoin m).glue_height_lower v
    have old := (lower.vertex_inside v).2.2
    rw [(upperJoin m).glue_height_lower, inner]
    unfold halfHeight
    linarith [hy.1]
  | right v =>
    have old := (upper.vertex_inside v).2.1
    have height : (upperJoin m).glue.vertexHeight (Fin.natAdd L v) =
        halfHeight 1 (upper.vertexHeight v) := (upperJoin m).glue_height_upper v
    rw [height]
    unfold halfHeight
    linarith [hy.2]

noncomputable def middleSweep : (lowerJoin m).glue.LayerSweep := (lowerJoin m).glue.layerSweep

variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : (glueCollar m).LayerSweep)

theorem collar_first_word : s.word 0 = p.word 0 :=
  ((upperJoin m).sweep_first_word (middleSweep m) s).trans
    ((lowerJoin m).sweep_first_word p (middleSweep m))

theorem collar_last_word :
    s.word (Fin.last (glueCollar m).levelCount) = q.word (Fin.last upper.levelCount) :=
  (upperJoin m).sweep_last_word q s

include m in
theorem collar_join_word : q.word 0 = p.word (Fin.last lower.levelCount) :=
  ((upperJoin m).sweep_join_word (middleSweep m) q).trans
    (((lowerJoin m).sweep_last_word (collar m).layerSweep (middleSweep m)).trans
      ((vertex_free_word (collar m).layerSweep).trans ((lowerJoin m).sweep_join_word p (collar m).layerSweep)))

private theorem partial_cells {V U X Y : ℕ} {a : ProgressiveGraph.Diagram S V X .point}
    {b : ProgressiveGraph.Diagram S U Y .point} (j : a.PartialVerticalMatch b)
    (p : a.LayerSweep) (q : b.LayerSweep) (s : j.glue.LayerSweep) :
    s.sheet.cells = p.sheet.cells ++ q.sheet.cells := by
  simpa only [Sheet.cells_reindex, cells_thenDo] using
    congrArg Sheet.cells (j.sweep_concat p q s)

theorem collar_concat :
    s.sheet.reindex (collar_first_word m p s) (collar_last_word m q s) =
      p.sheet.thenDo (q.sheet.reindex (collar_join_word m p q) rfl) := by
  apply concat_of_cells p q s
  calc
    _ = (middleSweep m).sheet.cells ++ q.sheet.cells :=
      partial_cells (upperJoin m) (middleSweep m) q s
    _ = (p.sheet.cells ++ (collar m).layerSweep.sheet.cells) ++ q.sheet.cells :=
      congrArg (· ++ q.sheet.cells) (partial_cells (lowerJoin m) p (collar m).layerSweep (middleSweep m))
    _ = _ := by rw [vertex_free_cells, List.append_nil]

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
