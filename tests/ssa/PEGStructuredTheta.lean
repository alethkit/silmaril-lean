module

import Silmaril.SSA.PEG.Bridge.Theta.Thms

namespace Silmaril.SSA.PEG.Bridge.Theta.Tests

open RVSDG (Tuple)

private abbrev Acc : Ty Unit := .data ()

private inductive Instr : InstructionSet.{0,0} Unit
  | stop : Instr [.count, Acc] .bool
  | never : Instr [.count, Acc] .bool
  | bump : Instr [.count, Acc] .count
  | addOldCount : Instr [.count, Acc] Acc

private def values : TotalModel Instr where
  carrier _ := Nat
  run
    | .stop, .cons counter _ => ⟨decide (2 ≤ counter.down)⟩
    | .never, _ => ⟨false⟩
    | .bump, .cons counter _ => ⟨counter.down + 1⟩
    | .addOldCount, .cons counter (.cons sum .nil) => Nat.add sum counter.down + 1

private def loop : Loop Instr .count Acc := ⟨.stop, .bump, .addOldCount⟩

private def form : Form loop.peg := ⟨loop, rfl⟩

private def pair (counter sum : Nat) : Tuple values.toPEG.Value [.count, Acc] :=
  .cons ⟨counter⟩ (.cons sum .nil)

private def idx : Index 1 := fun _ => 0

private theorem firstExit : loop.FirstExit values (pair 0 5) 2 := by
  refine ⟨rfl, fun j hj => ?_⟩
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl <;> rfl

-- Two continue activations. Both updates use the old counter.
example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 0 5)) =
    RVSDG.Theta.bodyResult (model values .count Acc) true (encodeCarried values (pair 1 6)) := rfl

example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 1 6)) =
    RVSDG.Theta.bodyResult (model values .count Acc) true (encodeCarried values (pair 2 8)) := rfl

-- Exit returns the old tuple unchanged, rather than feeding back (3, 11).
example : (compile form).body.run (model values .count Acc) (encodeCarried values (pair 2 8)) =
    RVSDG.Theta.bodyResult (model values .count Acc) false (encodeCarried values (pair 2 8)) := rfl

private theorem returned :
    (compile form).Returns (model values .count Acc) (encodeCarried values (pair 0 5))
      (encodeCarried values (pair 2 8)) := by
  apply RVSDG.Theta.Iterate.again (next := encodeCarried values (pair 1 6))
  · rfl
  apply RVSDG.Theta.Iterate.again (next := encodeCarried values (pair 2 8))
  · rfl
  exact RVSDG.Theta.Iterate.stop rfl

example : loop.peg.denote values.toPEG (pair 0 5) loop.demandWellFounded (5, idx) = some ⟨2⟩ :=
  (loop.pass_eq_some_iff values (pair 0 5) idx 2 loop.demandWellFounded).mpr firstExit

example : loop.peg.observe values.toPEG
    (loop.peg.denote values.toPEG (pair 0 5) loop.demandWellFounded) idx =
      (pair 2 8).map (fun _ => some) :=
  (returns_iff_observe values (pair 0 5) form idx loop.demandWellFounded (pair 2 8)).mp returned

example : (compile form).denotePart (model values .count Acc) (encodeCarried values (pair 0 5)) =
    Part.some (RVSDG.Categorical.pack (encodeCarried values (pair 2 8))) :=
  (compile form).denotePart_eq_some (model values .count Acc) _ _ |>.mpr returned

-- Entering already at the stopping bound still executes one body activation.
example : (compile form).Returns (model values .count Acc) (encodeCarried values (pair 2 99))
    (encodeCarried values (pair 2 99)) :=
  RVSDG.Theta.Iterate.stop rfl

private def noExit : Loop Instr .count Acc := ⟨.never, .bump, .addOldCount⟩

example (output : Tuple values.toPEG.Value [.count, Acc]) :
    ¬ noExit.toTheta.Returns (model values .count Acc) (encodeCarried values (pair 0 5))
      (encodeCarried values output) := by
  intro h
  obtain ⟨k, first, _⟩ := (noExit.returns_iff_firstExit values (pair 0 5) output).mp h
  have impossible : false = true := first.1
  contradiction

end Silmaril.SSA.PEG.Bridge.Theta.Tests
