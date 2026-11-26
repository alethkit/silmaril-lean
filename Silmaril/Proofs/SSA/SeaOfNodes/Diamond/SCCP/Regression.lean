module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example.Defs

namespace Silmaril.SSA.SeaOfNodes.Diamond.SCCP

open Example

-- The unreachable operand is a different constant and would overdefine Phi if joined.
example : report .onFalse (.constant ⟨true⟩) = (false, true, .constant 14) := by decide
example : report .onTrue (.constant ⟨true⟩) = (true, false, .constant 14) := by decide
example : report .onFalse (.constant ⟨false⟩) = (true, false, .constant 99) := by decide

-- An unclassified concrete guard permits both occurrences.
example : report .onFalse .overdefined = (true, true, .overdefined) := by decide

-- Bottom records absence of evidence and is distinct from a runtime-unknown guard.
example : report .onFalse .bottom = (false, false, .bottom) := by decide

example : (graph .onFalse).denote model (.cons ⟨true⟩ .nil) = (14 : Nat) := rfl
example : (graph .onFalse).denote model (.cons ⟨false⟩ .nil) = (99 : Nat) := rfl

end Silmaril.SSA.SeaOfNodes.Diamond.SCCP
