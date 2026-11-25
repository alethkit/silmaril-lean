module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepFrontiers
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepRows

public section

namespace Silmaril.RuntimeWires.Proofs.ProgressiveGluing

open ProgressiveGraph ProgressiveGraph.Diagram
open Sliced (Row Sheet)

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B C : ℕ}

private theorem cells_joinRows {n : ℕ} (word : Fin (n + 1) → List O)
    (row : ∀ i : Fin n, Row S (word i.castSucc) (word i.succ)) :
    (ProgressiveGraph.Diagram.Sweep.joinRows word row).cells = List.ofFn (fun i => (row i).cells) := by
  induction n with
  | zero =>
    exact (Sheet.cells_empty (S := S) (A := word 0)).trans
      (List.ofFn_zero (f := fun i : Fin 0 => (row i).cells)).symm
  | succ n ih =>
    calc
      _ = (row 0).cells ::
          (ProgressiveGraph.Diagram.Sweep.joinRows (word ∘ Fin.succ) (fun i => row i.succ)).cells :=
        Sheet.cells_cons (row 0) _
      _ = (row 0).cells :: List.ofFn (fun i => (row i.succ).cells) :=
        congrArg (List.cons (row 0).cells) (ih (word ∘ Fin.succ) (fun i => row i.succ))
      _ = _ := (List.ofFn_succ (f := fun i : Fin (n + 1) => (row i).cells)).symm

private theorem cells_thenDo {A B C : List O} (p : Sheet S A B) (q : Sheet S B C) :
    (p.thenDo q).cells = p.cells ++ q.cells := by
  induction p with
  | empty => simp only [Sheet.thenDo, Sheet.cells_empty, List.nil_append]
  | cons row p ih => simp only [Sheet.thenDo, Sheet.cells_cons, ih, List.cons_append]

private theorem ofFn_cast {α : Type*} {n k : ℕ} (eq : n = k) (f : Fin n → α) :
    List.ofFn f = List.ofFn (fun i : Fin k => f (i.cast eq.symm)) := by
  subst k
  rfl

section

variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable {g : ProgressiveGraph.Diagram S (L + R) C .point}
variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : g.LayerSweep)

theorem sweep_cells (stack : LevelStack lower upper g)
    (lower_rows : ∀ i, (s.row (stack.lowerLevel i)).cells = (p.row i).cells)
    (upper_rows : ∀ i, (s.row (stack.upperLevel i)).cells = (q.row i).cells) :
    s.sheet.cells = p.sheet.cells ++ q.sheet.cells := by
  simp only [LayerSweep.sheet, cells_joinRows]
  rw [ofFn_cast (stack.count_glue), List.ofFn_add]
  have left : (List.ofFn fun i : Fin lower.levelCount =>
      (s.row ((i.castLE (Nat.le_add_right _ upper.levelCount)).cast (stack.count_glue).symm)).cells) =
      List.ofFn (fun i => (p.row i).cells) := by
    apply congrArg List.ofFn
    funext i
    have eq : (i.castLE (Nat.le_add_right _ upper.levelCount)).cast (stack.count_glue).symm =
        stack.lowerLevel i := Fin.ext rfl
    rw [eq, lower_rows]
  have right : (List.ofFn fun i : Fin upper.levelCount =>
      (s.row ((i.natAdd lower.levelCount).cast (stack.count_glue).symm)).cells) =
      List.ofFn (fun i => (q.row i).cells) := by
    apply congrArg List.ofFn
    funext i
    have eq : (i.natAdd lower.levelCount).cast (stack.count_glue).symm =
        stack.upperLevel i := Fin.ext rfl
    rw [eq, upper_rows]
  rw [left, right]

theorem concat_of_cells
    (first : s.word 0 = p.word 0) (last : s.word (Fin.last g.levelCount) = q.word (Fin.last upper.levelCount))
    (join : q.word 0 = p.word (Fin.last lower.levelCount))
    (cells : s.sheet.cells = p.sheet.cells ++ q.sheet.cells) :
    s.sheet.reindex first last = p.sheet.thenDo (q.sheet.reindex join rfl) := by
  apply Sheet.cells_injective
  simpa only [Sheet.cells_reindex, cells_thenDo] using cells

end

variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R A .point}
variable (m : lower.VerticalMatch upper)
variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem first_word : s.word 0 = p.word 0 := by
  simp only [LayerSweep.word, wires_first m p s, m.glue_label_lower]

theorem last_word : s.word (Fin.last m.glue.levelCount) = q.word (Fin.last upper.levelCount) := by
  simp only [LayerSweep.word, wires_last m q s, m.glue_label_upper]

include m in
theorem join_word : q.word 0 = p.word (Fin.last lower.levelCount) := by
  have ids := ProgressiveGraph.Diagram.ordered_cut_unique (ordered_join_upper m q) (ordered_join_lower m p)
  simp only [LayerSweep.word, ids, funext m.label]

theorem sweep_concat :
    (s.sheet.reindex (first_word m p s) (last_word m q s)) =
      p.sheet.thenDo (q.sheet.reindex (join_word m p q) rfl) :=
  concat_of_cells p q s _ _ _
    (sweep_cells p q s (matchedStack m) (row_cells_lower m p s) (row_cells_upper m q s))

end Silmaril.RuntimeWires.Proofs.ProgressiveGluing
