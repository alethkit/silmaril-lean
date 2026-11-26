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
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {src : Source Op regs out} {entry : Fin 6}
variable (p : Program src entry) (m : Model.{u, v, w} Op)

/-- Each γ child uses the ordered quads at its original predecessor ID. -/
theorem Program.arm_body (occurrence : Fin 2) :
    p.stage.table.get occurrence = (src (p.predecessor occurrence)).body :=
  Proofs.arm_body p occurrence

/-- The γ tag preserves which occurrence the source conditional selects. -/
theorem Program.selected_predecessor (bank : Bank (regs := regs) m) :
    p.predecessor (p.stage.choice.eval bank) =
      (if (bank.get p.condition).down then p.onTrue else p.onFalse) :=
  Proofs.selected_predecessor p m bank

/-- The actual γ merge produces all reaching values from the selected
occurrence. No value from the unselected predecessor enters this bank. -/
theorem Program.merge_run (bank : Bank (regs := regs) m) :
    p.plan.lower.run (model m) bank =
      (src (p.predecessor (p.stage.choice.eval bank))).body.eval m bank := by
  rw [Plan.lower_run]
  exact congrArg (fun block : Block Op regs => block.eval m bank) (p.arm_body _)

/-- After the merge and latch, θ sees the exact updated bank and source test. -/
theorem Program.activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    p.thetaBody.run (model m) fuel old =
      some (RVSDG.Theta.bodyResult (model m) ((p.nextBank m old).get p.again).down (p.nextBank m old)) :=
  Proofs.body_run p m fuel old

/-- Entry costs one source visit. Each θ activation costs four source visits,
and a shorter surplus cannot reach another tested latch. -/
theorem Program.lower_run (fuel extra : Nat) (short : extra < 4) (input : Bank (regs := regs) m) :
    p.lower.run (model m) fuel input =
      (src.runFrom m (extra + 4 * fuel + 1) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m fuel extra short input

theorem Program.returns_iff (input : Bank (regs := regs) m) (result : sortValue m.value out) :
    p.lower.Returns (model m) input (.cons result .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some result :=
  Proofs.returns_iff p m input result

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond
