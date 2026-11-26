module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA

open Example
open Diamond.LambdaSSA (encodeTuple inputEnv instruction)
open Isotope.LambdaSSA.Semantics.Region (Eval Follow)
open SeaOfNodes.Loop.LambdaSSA

example : (lower program).HasType (Generic.inputContext regs) [Generic.packed [.value num]] :=
  lower_hasType program

private abbrev entryEdge := Generic.edge program.lower .entry
private abbrev feedbackEdge := Generic.edge program.lower .backedge

example : entryEdge.target = feedbackEdge.target := rfl
example : entryEdge ≠ feedbackEdge := incoming_distinct program

-- The entry x operand reads the preheader's newest let. Feedback x and y
-- read different header lets, both shifted by the unit binder of the case.
example : ((Generic.phiView program.lower).table.column entryEdge (1 : Fin 6)).val = 0 := rfl
example : ((Generic.phiView program.lower).table.column feedbackEdge (1 : Fin 6)).val = 4 := rfl
example : ((Generic.phiView program.lower).table.column feedbackEdge (2 : Fin 6)).val = 3 := rfl

example : program.evalBackedges arithmetic 0 (input 3) = none := rfl
example : program.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl
example : program.evalBackedges arithmetic 3 (input 3) = some (29 : Nat) := rfl
example : program.evalBackedges arithmetic 0 (input 1) = some (12 : Nat) := rfl

private theorem counted : program.lower.ReturnsAfter arithmetic (input 3) 2
    (program.initial arithmetic (input 3)) (29 : Nat) :=
  .backedge (next := bank 2 5 12 7 2 true) rfl
    (.backedge (next := bank 1 12 17 5 2 true) rfl (.exit rfl))

example (count : Nat) (within : count ≤ 1) (result : Nat) :
    ¬ program.lower.ReturnsAfter arithmetic (input 3) count
      (program.initial arithmetic (input 3)) result := by
  intro run
  have source := (returns_within_iff program arithmetic (input 3) 1 result).mpr ⟨count, within, run⟩
  cases source

-- This is the ordinary emitted continuation with its two-backedge source witness.
example : Follow (instruction arithmetic) (inputEnv arithmetic (input 3))
    (Generic.blocks program.lower) 0 (encodeTuple arithmetic (program.initial arithmetic (input 3)))
    (42 : Nat) 0 (.pair (.atom ⟨(), (29 : Nat)⟩) .unit) 42 :=
  (Generic.follow_iff program.lower arithmetic (input 3)
    (program.initial arithmetic (input 3)) 42 42 0 _).mpr ⟨2, (29 : Nat), counted, rfl, rfl, rfl⟩

example : Eval (instruction arithmetic) (inputEnv arithmetic (input 3)) (lower program)
    (42 : Nat) 0 (.pair (.atom ⟨(), (29 : Nat)⟩) .unit) 42 :=
  (returns_iff program arithmetic (input 3) 42 (29 : Nat)).mp ⟨2, rfl⟩

example : Eval (instruction arithmetic) (inputEnv arithmetic (input 1)) (lower program)
    (42 : Nat) 0 (.pair (.atom ⟨(), (12 : Nat)⟩) .unit) 42 :=
  (returns_iff program arithmetic (input 1) 42 (12 : Nat)).mp ⟨0, rfl⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA
