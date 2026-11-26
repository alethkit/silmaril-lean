module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Memory

/-!
# Queries of one memory32 instance

The isolated queries are `memory.size` and full-width `i32.load` at a supplied
unsigned static offset. The memory is supplied as bytes. An out-of-bounds load yields
the administrative trap; a missing memory is outside the native image.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

inductive State where
  | size
  | load (address : BitVec 32)
  | value (bits : BitVec 32)
  | trap

abbrev Judgment := State × State

inductive RuleInstanceAt (bytes : ByteArray) (offset : Nat) : Rule Judgment → Prop where
  | size : RuleInstanceAt bytes offset ⟨[], (.size, .value (BitVec.ofNat 32 (Memory.size bytes)))⟩
  | load (address bits : BitVec 32) (read : Memory.load bytes (address.toNat + offset) 4 = some bits) :
      RuleInstanceAt bytes offset ⟨[], (.load address, .value bits)⟩
  | loadTrap (address : BitVec 32) (bound : bytes.size < address.toNat + offset + 4) :
      RuleInstanceAt bytes offset ⟨[], (.load address, .trap)⟩

abbrev RuleInstance (bytes : ByteArray) := RuleInstanceAt bytes 0

abbrev RuleInstance.size {bytes : ByteArray} := RuleInstanceAt.size (bytes := bytes) (offset := 0)
abbrev RuleInstance.load {bytes : ByteArray} := RuleInstanceAt.load (bytes := bytes) (offset := 0)
abbrev RuleInstance.loadTrap {bytes : ByteArray} := RuleInstanceAt.loadTrap (bytes := bytes) (offset := 0)

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentationAt (bytes : ByteArray) (offset : Nat) : SOS.Presentation := ⟨shape, {r | RuleInstanceAt bytes offset r}⟩

abbrev presentation (bytes : ByteArray) := presentationAt bytes 0

abbrev EdgeAt (bytes : ByteArray) (offset : Nat) (a b : State) :=
  (presentationAt bytes offset).Derives (a, b)

abbrev Edge (bytes : ByteArray) := EdgeAt bytes 0

end Silmaril.Wasm.Institution.Operational.MemoryQuery
