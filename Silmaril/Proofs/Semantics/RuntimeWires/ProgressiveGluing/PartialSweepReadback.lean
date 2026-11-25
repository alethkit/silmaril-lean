module

public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.PartialSweepFrontiers
public import Silmaril.Proofs.Semantics.RuntimeWires.ProgressiveGluing.SweepReadback

public section

namespace Silmaril.RuntimeWires.Proofs.PartialGluing

open ProgressiveGraph ProgressiveGraph.Diagram

universe u v

variable {O : Type u} {S : Signature.{u,v} O} {L R A B : ℕ}
variable {lower : ProgressiveGraph.Diagram S L A .point} {upper : ProgressiveGraph.Diagram S R B .point}
variable (m : lower.PartialVerticalMatch upper)
variable (p : lower.LayerSweep) (q : upper.LayerSweep) (s : m.glue.LayerSweep)

theorem sweep_concat :
    s.sheet.reindex (first_word m p s) (last_word m q s) =
      p.sheet.thenDo (q.sheet.reindex (join_word m p q) rfl) :=
  Proofs.ProgressiveGluing.concat_of_cells p q s _ _ _
    (Proofs.ProgressiveGluing.sweep_cells p q s (sweepStack m)
      (row_cells_lower m p s) (row_cells_upper m q s))

theorem sweep_serial_concat (pp : p.Schedule) (qp : q.Schedule) (sp : s.Schedule) :
    Sliced.Sheet.SeamEquivalent
      ((s.serialSheet sp).reindex (first_word m p s) (last_word m q s))
      ((p.serialSheet pp).thenDo ((q.serialSheet qp).reindex (join_word m p q) rfl)) := by
  have glued := (s.serial_seam sp).reindex (first_word m p s) (last_word m q s)
  have operands := (p.serial_seam pp).thenDo ((q.serial_seam qp).reindex (join_word m p q) rfl)
  rw [← sweep_concat m p q s] at operands
  exact .trans _ _ _ glued (.symm _ _ operands)

end Silmaril.RuntimeWires.Proofs.PartialGluing
