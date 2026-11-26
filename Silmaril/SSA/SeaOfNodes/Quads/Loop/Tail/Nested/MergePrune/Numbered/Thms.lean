module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Correctness

/-! # The smaller γ bank preserves the selected inputs and the complete loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult nextBank sourceVisits)
open Join (model)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry)

/-- The chosen numbered route sends exactly its projected incoming column. -/
theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p projected merge).toGraph.run (model m) fuel (carry.project old) =
      some (incoming p merge m old (p.selected m old)) :=
  Proofs.merge_run p m projected fuel old

/-- The emitted smaller γ needs agreement only on the latch packet. -/
theorem activation_run_for
    (agrees : ∀ left right : Bank (regs := regs) m, merge.project left = merge.project right →
      latchPacket p carry m ((Nested.Numbered.tail p).eval m left) =
        latchPacket p carry m ((Nested.Numbered.tail p).eval m right))
    (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBodyFor p projected merge).run (model m) fuel (carry.project old) =
      some (latchPacket p carry m (nextBank p m old)) :=
  Proofs.activation_run_for p m projected agrees fuel old

variable (checked : Checked p merge)

/-- Reconstruction recovers the exact original stop tag and feedback bank. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked).run (model m) fuel (carry.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (carry.project next)) :=
  Proofs.activation_run p m projected checked fuel old

variable (result : KeptResult p (mask := carry))

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected checked result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Nested.Numbered.lowerWith_run p m _ (activation_run p m projected checked) result fuel input

/-- The original numbered graph and the smaller γ agree at every θ budget. -/
theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected checked result).run (model m) fuel input =
      (Nested.Numbered.lower p projected result).run (model m) fuel input :=
  (lower_run p m projected checked result fuel input).trans
    (Nested.Numbered.lower_run p m projected result fuel input).symm

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p projected checked result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  (exists_congr fun fuel => by rw [run_agrees p m projected checked result fuel input]).trans
    (Nested.Numbered.returns_iff p m projected result input value)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered
