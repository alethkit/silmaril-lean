module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Correctness

/-! # Selected occurrences and exact returns after θ interface projection -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Join (model)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (checked : Checked p mask) (m : Model.{u, v, w} Op)

/-- The reconstructed bank supplies the same tests and data to the shared γ. -/
theorem Checked.header_agrees (old : Bank (regs := regs) m) :
    checked.headerBank m (mask.project old) = (src p.header).body.eval m old :=
  Proofs.header_agrees checked m old

/-- The selected occurrences agree at every activation bound. Both traces
use the original program's map from occurrences to predecessor IDs. -/
theorem Checked.trace_agrees (fuel : Nat) (old : Bank (regs := regs) m) :
    checked.trace m fuel (mask.project old) = p.trace m fuel old :=
  Proofs.trace_agrees checked m fuel old

/-- The emitted body supplies the exact source stop or restart tag and
projects the full updated bank simultaneously. -/
theorem Checked.activation_agrees (fuel : Nat) (old : Bank (regs := regs) m) :
    checked.thetaBody.run (model m) fuel (mask.project old) =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down
        (mask.project (p.nextBank m old))) :=
  Proofs.activation_agrees checked m fuel old

theorem Checked.run_agrees (fuel : Nat) (input : Bank (regs := regs) m) :
    checked.lower.run (model m) fuel input = p.lower.run (model m) fuel input :=
  Proofs.run_agrees checked m fuel input

/-- Projection preserves the exact selected-arm source budget and exhaustion. -/
theorem Checked.lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    checked.lower.run (model m) fuel input =
      (src.runFrom m (p.sourceVisits m fuel input) entry input).map (fun value => .cons value .nil) :=
  (checked.run_agrees m fuel input).trans (p.lower_run m fuel input)

theorem Checked.run_at (fuel sourceFuel : Nat) (input : Bank (regs := regs) m)
    (result : sortValue m.value out)
    (returned : checked.lower.run (model m) fuel input = some (.cons result .nil)) :
    src.runFrom m sourceFuel entry input =
      if p.sourceVisits m fuel input ≤ sourceFuel then some result else none :=
  p.run_at m fuel sourceFuel input result ((checked.run_agrees m fuel input).symm.trans returned)

theorem Checked.returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    checked.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result :=
  (exists_congr fun fuel => by rw [checked.run_agrees m fuel input]).trans (p.returns_iff m input result)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune
