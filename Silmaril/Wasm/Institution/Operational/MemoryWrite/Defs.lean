module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Memory

/-! # An isolated Memory32 write

Full-width `i32.store` at static offset zero either writes four little-endian
bytes or traps on an out-of-bounds range. Successful execution leaves empty
code. The selected memory is part of the native boundary data.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution

inductive State where
  | store (address word : BitVec 32)
  | written (bytes : ByteArray)
  | trap

abbrev Judgment := State × State

inductive Outcome (bytes : ByteArray) : State → State → Prop where
  | write (address word : BitVec 32) (out : ByteArray)
      (stored : Memory.store bytes address.toNat (count := 4) word = some out) :
      Outcome bytes (.store address word) (.written out)
  | trap (address word : BitVec 32) (oob : bytes.size < address.toNat + 4) :
      Outcome bytes (.store address word) .trap

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentation (bytes : ByteArray) : SOS.Presentation :=
  ⟨shape, {r | r.premises = [] ∧ Outcome bytes r.conclusion.1 r.conclusion.2}⟩

abbrev Edge (bytes : ByteArray) (a b : State) := (presentation bytes).Derives (a, b)
abbrev Runs (bytes : ByteArray) := Relation.ReflTransGen (Edge bytes)

def Admitted (bytes : ByteArray) : State → Prop
  | .written out => out.size = bytes.size
  | _ => True

end Silmaril.Wasm.Institution.Operational.MemoryWrite
