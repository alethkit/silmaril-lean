module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Correctness

/-! # Occurrence-resolved γ banks and finite returns of the numbered θ -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Diamond.Prune (HeaderProjection)
open Join (model)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body mask)

/-- The two emitted γ selections supply the entire original source column
at whichever of the three incoming occurrences is selected. -/
theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p projected).toGraph.run (model m) fuel (mask.project old) =
      some (p.mergeBank m old (p.selected m old)) :=
  Proofs.merge_run p m projected fuel old

/-- A θ activation returns the post-latch stop tag and simultaneous projected feedback. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected).run (model m) fuel (mask.project old) =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down (mask.project next)) :=
  Proofs.activation_run p m projected fuel old

/-- One source visit per original block on the selected paths accounts for
the native bound, including runs that exhaust at that bound. -/
theorem lower_run (result : KeptResult p (mask := mask)) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected result).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m projected result fuel input

/-- A finite return of the original source is witnessed at some activation
bound in the emitted graph, and vice versa. -/
theorem returns_iff (result : KeptResult p (mask := mask)) (input : Bank (regs := regs) m)
    (value : sortValue m.value out) :
    (lower p projected result).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Proofs.returns_iff p m projected result input value

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered
