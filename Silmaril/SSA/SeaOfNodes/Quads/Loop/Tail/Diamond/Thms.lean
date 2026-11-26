module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Correctness

/-! # Source occurrences, simultaneous latching, and native finite returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Join (Block model)
open Join.Finite (Plan Stage Table)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

/-- Each γ child uses the ordered quads of its checked original arm. -/
theorem Program.arm_body (occurrence : Fin 2) :
    p.stage.table.get occurrence = (p.armPath occurrence).quads :=
  Proofs.arm_body p occurrence

/-- The γ tag preserves which occurrence the source conditional selects. -/
theorem Program.selected_predecessor (bank : Bank (regs := regs) m) :
    p.predecessor (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.trueArm.lastBlock else p.falseArm.lastBlock) :=
  Proofs.selected_predecessor p m bank

/-- The actual γ merge produces all reaching values from the selected
occurrence. No value from the unselected predecessor enters this bank. -/
theorem Program.merge_run (bank : Bank (regs := regs) m) :
    p.plan.lower.run (model m) bank =
      (p.armPath (p.stage.choice.eval bank)).quads.eval m bank := by
  rw [Plan.lower_run]
  exact congrArg (fun block : Block Op regs => block.eval m bank) (p.arm_body _)

/-- After the merge and latch, θ sees the exact updated bank and source test. -/
theorem Program.activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    p.thetaBody.run (model m) fuel old =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old)) :=
  Proofs.body_run p m fuel old

/-- Match a native budget with one entry visit and the sum of the selected
activation costs, even if the bounded native run exhausts. -/
theorem Program.lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (src.runFrom m (p.sourceVisits m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m fuel input

/-- A returning native trace gives the minimum source fuel for that return.
Every smaller source budget exhausts. -/
theorem Program.run_at (fuel sourceFuel : Nat) (input : Bank (regs := regs) m)
    (result : sortValue m.value out)
    (returned : p.lower.run (model m) fuel input = some (.cons result .nil)) :
    src.runFrom m sourceFuel entry input =
      if p.sourceVisits m fuel input ≤ sourceFuel then some result else none :=
  Proofs.run_at p m fuel sourceFuel input result returned

/-- A bounded source return has a native return whose selected trace fits
the source budget, and conversely. -/
theorem Program.source_bounded_iff (fuel : Nat) (input : Bank (regs := regs) m)
    (result : sortValue m.value out) :
    src.runFrom m fuel entry input = some result ↔
      ∃ activations, p.lower.run (model m) activations input = some (.cons result .nil) ∧
        p.sourceVisits m activations input ≤ fuel :=
  Proofs.source_bounded_iff p m fuel input result

theorem Program.returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    p.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result :=
  Proofs.returns_iff p m input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
