module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs

open Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

theorem invert_at {bytes : ByteArray} {offset : Nat} {a b : State} (edge : EdgeAt bytes offset a b) :
    RuleInstanceAt bytes offset ⟨[], (a, b)⟩ := by
  refine Derives.least (M := fun j => RuleInstanceAt bytes offset ⟨[], j⟩) edge ?_
  intro r member _
  change RuleInstanceAt bytes offset r at member
  cases member with
  | size => exact .size
  | load a v h => exact .load a v h
  | loadTrap a h => exact .loadTrap a h

theorem load_none_iff_at {bytes : ByteArray} {offset : Nat} {address : BitVec 32} :
    Memory.load bytes (address.toNat + offset) 4 = none ↔ bytes.size < address.toNat + offset + 4 := by
  by_cases bound : address.toNat + offset + 4 ≤ bytes.size <;>
    simp [Memory.load, Memory.readBytes, bound, Nat.not_lt.mpr, Nat.lt_of_not_ge]

end Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs
