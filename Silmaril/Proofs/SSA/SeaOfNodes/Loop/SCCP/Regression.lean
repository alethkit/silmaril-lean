module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

-- Entry supplies 0. After the backedge becomes executable, feedback 1 widens the latch.
example : changingLatch 2 = .constant 0 := by decide
example : changingLatch 3 = .constant 0 := by decide
example : changingLatch 4 = .overdefined := by decide
example : report 1 (.constant ⟨true⟩) = (true, true, true, .overdefined, .overdefined) := by decide
example : run 1 true 1 = none := by decide
example : run 1 true 2 = some 3 := by decide

-- Both successors are possible with an unclassified external flag. Feedback 0 preserves the constant.
example : report 0 .overdefined = (true, true, true, .constant 0, .constant 0) := by decide
example : run 0 false 0 = some 0 := by decide
example : Arrives model (graph 0) (entry 0 true) .backedge 2 (.cons (0 : Byte) .nil) :=
  .backedge (.backedge .entry rfl) rfl

-- When only exit can execute, an unequal feedback operand does not pollute Phi.
example : report 1 (.constant ⟨false⟩) = (true, false, true, .constant 0, .constant 1) := by decide
example : run 1 false 0 = some 1 := by decide

-- Flag and word share the same edges and have separate flat facts.
example : Example.Bank.invariantReport = (true, true, (.constant true, .overdefined), .overdefined) := by decide
example : Example.Bank.runInvariant 1 = none := by decide
example : Example.Bank.runInvariant 2 = some 3 := by decide

-- Both new fields read the old bank. Reading the new flag when computing
-- the word would increment it from 0 to 1.
example : Example.Bank.abstractCrossFeedback = (.constant true, .constant 0) := by decide
example : Example.Bank.nativeCrossFeedback = some (true, 0) := by decide
example : Arrives Example.Bank.model (Example.Bank.graph true) (Example.Bank.entry false 0)
    .backedge 1 (Example.Bank.entry true 0) := .backedge .entry rfl

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
