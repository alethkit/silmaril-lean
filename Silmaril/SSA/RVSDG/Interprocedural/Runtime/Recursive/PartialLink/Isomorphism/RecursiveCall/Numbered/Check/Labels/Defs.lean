module

public import Silmaril.SSA.RVSDG.Interprocedural.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs

/-! Executable equality of interprocedural port types and instruction labels. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered

open NestedTheta.Equality (OpcodeCode)

universe u v

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}

section PortEquality

variable [DecidableEq V] [DecidableEq S]

mutual

def decideValue : (a b : ValueSort V S) → Decidable (a = b)
  | .data x, .data y => decidable_of_iff (x = y)
      ⟨congrArg ValueSort.data, ValueSort.data.inj⟩
  | .function a r, .function b s => by
    letI := decidePorts a b
    letI := decidePorts r s
    exact decidable_of_iff (a = b ∧ r = s) ⟨fun ⟨rfl, rfl⟩ => rfl, ValueSort.function.inj⟩
  | .global x, .global y => by
    letI := decideValue x y
    exact decidable_of_iff (x = y) ⟨congrArg ValueSort.global, ValueSort.global.inj⟩
  | .data _, .function .. | .data _, .global _ | .function .., .data _ | .function .., .global _
  | .global _, .data _ | .global _, .function .. => .isFalse (by intro h; cases h)
termination_by a _ => sizeOf a

/-- Decide interprocedural port equality recursively through callable
signatures and global payload types. -/
def decidePort : (a b : Ty V S) → Decidable (a = b)
  | .value a, .value b => by
    letI := decideValue a b
    exact decidable_of_iff (a = b) ⟨congrArg PortType.value, PortType.value.inj⟩
  | .control a, .control b => decidable_of_iff (a = b) ⟨congrArg PortType.control, PortType.control.inj⟩
  | .state a, .state b => decidable_of_iff (a = b) ⟨congrArg PortType.state, PortType.state.inj⟩
  | .value _, .control _ | .value _, .state _ | .control _, .value _ | .control _, .state _
  | .state _, .value _ | .state _, .control _ => .isFalse (by intro h; cases h)
termination_by a _ => sizeOf a

def decidePorts : (a b : Ports (Ty V S)) → Decidable (a = b)
  | [], [] => .isTrue rfl
  | [], _ :: _ | _ :: _, [] => .isFalse (by intro h; cases h)
  | a :: as, b :: bs => by
    letI := decidePort a b
    letI := decidePorts as bs
    exact decidable_of_iff (a = b ∧ as = bs) ⟨fun ⟨rfl, rfl⟩ => rfl, List.cons.inj⟩
termination_by a _ => sizeOf a

end

end PortEquality

def instructionKey (code : OpcodeCode Op) {ins outs : Ports (Ty V S)} :
    Instruction Op ins outs → Sum code.Key (Ports (Ty V S) × Ports (Ty V S))
  | .primitive opcode => .inl (code.encode opcode)
  | .apply fn => .inr (fn.args, fn.results)

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered
