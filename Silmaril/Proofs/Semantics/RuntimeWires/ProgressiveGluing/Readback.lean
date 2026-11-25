module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.Cuts
public import Silmaril.Semantics.RuntimeWires.SlicedCompleteness.Thms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram Sliced

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {W : ℕ}
variable {lower upper : ProgressiveGraph.Diagram S 1 W .point}
variable (m : lower.VerticalMatch upper)
variable {a b c d : ℝ}

include m in
private theorem all_after (e : lower.EventSlice 0 a b) (isolates : lower.Isolates 0 a b) :
    ∀ w, w ∈ e.afterWires := by
  intro w
  apply (e.after.exact_wires w).mpr
  have positive := (lower.vertex_inside 0).2.1.trans isolates.above
  have lowerBound : lower.lower w < b := by
    cases start : lower.start w with
    | none => simpa [ProgressiveGraph.Diagram.lower, endpointHeight, start] using positive
    | some j =>
      have eq : j = 0 := Subsingleton.elim j 0
      simpa [ProgressiveGraph.Diagram.lower, endpointHeight, start, eq] using isolates.above
  have upperBound : b < lower.upper w := by
    simpa [ProgressiveGraph.Diagram.upper, endpointHeight, m.lower_cap] using isolates.hi_inside
  exact ⟨lowerBound, upperBound⟩

include m in
private theorem all_before (e : upper.EventSlice 0 c d) (isolates : upper.Isolates 0 c d) :
    ∀ w, w ∈ e.beforeWires := by
  intro w
  apply (e.before.exact_wires w).mpr
  have belowOne := isolates.below.trans (upper.vertex_inside 0).2.2
  have lowerBound : upper.lower w < c := by
    simpa [ProgressiveGraph.Diagram.lower, endpointHeight, m.upper_cap] using isolates.lo_inside
  have upperBound : c < upper.upper w := by
    cases finish : upper.finish w with
    | none => simpa [ProgressiveGraph.Diagram.upper, endpointHeight, finish] using belowOne
    | some j =>
      have eq : j = 0 := Subsingleton.elim j 0
      simpa [ProgressiveGraph.Diagram.upper, endpointHeight, finish, eq] using isolates.below
  exact ⟨lowerBound, upperBound⟩

theorem lower_isolates (iso : lower.Isolates 0 a b) :
    m.glue.Isolates (Fin.castAdd 1 (0 : Fin 1)) (halfHeight 0 a) (1 / 2) := by
  have lo : 0 < halfHeight 0 a := by
    dsimp only [halfHeight]
    linarith [iso.lo_inside]
  refine ⟨lo, ?_, ?_, by norm_num, ?_⟩
  · rw [m.glue_height_left]
    exact halfHeight_strictMono 0 iso.below
  · rw [m.glue_height_left]
    dsimp only [halfHeight]
    linarith [(lower.vertex_inside 0).2.2]
  · intro j here
    induction j using Fin.addCases with
    | left v => exact congrArg (Fin.castAdd 1) (Subsingleton.elim v 0)
    | right v =>
      have hi := here.2
      rw [m.glue_height_right] at hi
      dsimp only [halfHeight] at hi
      exact (by linarith [(upper.vertex_inside v).2.1] : False).elim

theorem upper_isolates (iso : upper.Isolates 0 c d) :
    m.glue.Isolates (Fin.natAdd 1 (0 : Fin 1)) (1 / 2) (halfHeight 1 d) := by
  have hi : halfHeight 1 d < 1 := by
    dsimp only [halfHeight]
    linarith [iso.hi_inside]
  refine ⟨by norm_num, ?_, ?_, hi, ?_⟩
  · rw [m.glue_height_right]
    dsimp only [halfHeight]
    linarith [(upper.vertex_inside 0).2.1]
  · rw [m.glue_height_right]
    exact halfHeight_strictMono 1 iso.above
  · intro j here
    induction j using Fin.addCases with
    | left v =>
      have lo := here.1
      rw [m.glue_height_left] at lo
      dsimp only [halfHeight] at lo
      exact (by linarith [(lower.vertex_inside v).2.2] : False).elim
    | right v => exact congrArg (Fin.natAdd 1) (Subsingleton.elim v 0)

variable (e : lower.EventSlice 0 a b) (f : upper.EventSlice 0 c d)
variable (ea : lower.Isolates 0 a b) (fa : upper.Isolates 0 c d)

/-- Read the original event rows at the rescaled exterior cuts and the actual join. -/
def paired : m.glue.TwoEventSlice (Fin.castAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1))
    (halfHeight 0 a) (1 / 2) (halfHeight 1 d) where
  firstEvent := event_left m e (ea.below.trans (lower.vertex_inside 0).2.2) ea.hi_inside (all_after m e ea)
  secondEvent := event_right m f fa.lo_inside ((upper.vertex_inside 0).2.1.trans fa.above) (all_before m f fa)

theorem input_ids :
    (paired m e f ea fa).firstEvent.beforeWires = e.beforeWires := by
  change e.left ++ m.glue.inputs (Fin.castAdd 1 0) ++ e.right = e.beforeWires
  rw [m.glue_inputs_left]
  rfl

theorem output_ids :
    (paired m e f ea fa).secondEvent.afterWires = f.afterWires := by
  change f.left ++ m.glue.outputs (Fin.natAdd 1 0) ++ f.right = f.afterWires
  rw [m.glue_outputs_right]
  rfl

include m ea fa in
theorem join_ids : f.beforeWires = e.afterWires :=
  (ProgressiveGraph.Diagram.ordered_cut_unique
    (join_from_lower m e.after ea.hi_inside (all_after m e ea))
    (join_from_upper m f.before fa.lo_inside (all_before m f fa))).symm

private theorem event_cells {V : ℕ} {g : ProgressiveGraph.Diagram S V W .point} {j : Fin V} {a b : ℝ}
    (e : g.EventSlice j a b) :
    e.row.cells = (e.left.map g.label).map Sum.inl ++
      (Sum.inr (g.generator j) :: (e.right.map g.label).map Sum.inl) := by
  simp only [EventSlice.row, Row.cells_pass, Row.cells_box, Row.cells_straight]

private theorem single_cells {V : ℕ} {g : ProgressiveGraph.Diagram S V W .point} {j : Fin V} {a b : ℝ}
    (e : g.EventSlice j a b) : (Sheet.cons e.cutRow (.empty _)).cells = [e.row.cells] := by
  have cast_eq {A B X Y : List O} (r : Row S A B) (hA : A = X) (hB : B = Y) :
      r.reindex hA hB = (congrArg₂ (Row S) hA hB).mp r := by
    subst hA
    subst hB
    rfl
  have cells := Sheet.cells_reindex e.before_word.symm e.after_word.symm (Sheet.cons e.row (.empty _))
  rw [Sheet.reindex_single, cast_eq] at cells
  simpa only [EventSlice.cutRow, Sheet.cells_cons, Sheet.cells_empty] using cells

private theorem then_cells {A B C : List O} (p : Sheet S A B) (q : Sheet S B C) :
    (p.thenDo q).cells = p.cells ++ q.cells := by
  induction p with
  | empty => simp only [Sheet.thenDo, Sheet.cells_empty, List.nil_append]
  | cons row p ih => simp only [Sheet.thenDo, Sheet.cells_cons, ih, List.cons_append]

private theorem same_row_left :
    (paired m e f ea fa).firstEvent.row.cells = e.row.cells := by
  rw [event_cells, event_cells]
  change (e.left.map m.glue.label).map Sum.inl ++
    (Sum.inr (m.glue.generator (Fin.castAdd 1 0)) :: (e.right.map m.glue.label).map Sum.inl) = _
  rw [m.glue_generator_left, m.glue_label_lower]

private theorem same_row_right :
    (paired m e f ea fa).secondEvent.row.cells = f.row.cells := by
  rw [event_cells, event_cells]
  change (f.left.map m.glue.label).map Sum.inl ++
    (Sum.inr (m.glue.generator (Fin.natAdd 1 0)) :: (f.right.map m.glue.label).map Sum.inl) = _
  rw [m.glue_generator_right, m.glue_label_upper]

include ea fa in
theorem concat_readback :
    ∃ (g : m.glue.TwoEventSlice (Fin.castAdd 1 (0 : Fin 1)) (Fin.natAdd 1 (0 : Fin 1))
        (halfHeight 0 a) (1 / 2) (halfHeight 1 d))
      (first : g.firstEvent.beforeWires.map m.glue.label = e.beforeWires.map lower.label)
      (last : g.secondEvent.afterWires.map m.glue.label = f.afterWires.map upper.label)
      (join : f.beforeWires.map upper.label = e.afterWires.map lower.label),
      g.sheet.reindex first last =
        (Sheet.cons e.cutRow (.empty _)).thenDo ((Sheet.cons f.cutRow (.empty _)).reindex join rfl) := by
  have first : (paired m e f ea fa).firstEvent.beforeWires.map m.glue.label = e.beforeWires.map lower.label := by
    rw [input_ids, m.glue_label_lower]
  have last : (paired m e f ea fa).secondEvent.afterWires.map m.glue.label = f.afterWires.map upper.label := by
    rw [output_ids, m.glue_label_upper]
  have join : f.beforeWires.map upper.label = e.afterWires.map lower.label := by
    rw [join_ids m e f ea fa, funext m.label]
  refine ⟨paired m e f ea fa, first, last, join, Sheet.cells_injective ?_⟩
  rw [Sheet.cells_reindex first last, then_cells, single_cells e,
    Sheet.cells_reindex join rfl (Sheet.cons f.cutRow (.empty _)), single_cells f]
  have cells : (paired m e f ea fa).sheet.cells =
      [(paired m e f ea fa).firstEvent.row.cells, (paired m e f ea fa).secondEvent.row.cells] := by
    simp only [TwoEventSlice.sheet, Sheet.cells_reindex, Sheet.cells_cons, Sheet.cells_empty]
  rw [cells, same_row_left, same_row_right]
  rfl

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
