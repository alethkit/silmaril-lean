module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Memory

/-! # An isolated Memory32 write

Full-width `i32.store` with an unsigned static offset either writes four little-endian
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

inductive OutcomeAt (bytes : ByteArray) (offset : Nat) : State → State → Prop where
  | write (address word : BitVec 32) (out : ByteArray)
      (stored : Memory.store bytes (address.toNat + offset) (count := 4) word = some out) :
      OutcomeAt bytes offset (.store address word) (.written out)
  | trap (address word : BitVec 32) (oob : bytes.size < address.toNat + offset + 4) :
      OutcomeAt bytes offset (.store address word) .trap

abbrev Outcome (bytes : ByteArray) := OutcomeAt bytes 0

abbrev Outcome.write {bytes : ByteArray} := OutcomeAt.write (bytes := bytes) (offset := 0)
abbrev Outcome.trap {bytes : ByteArray} := OutcomeAt.trap (bytes := bytes) (offset := 0)

def shape : SOS.Shape.{0} := ⟨⟨State, Unit⟩, Judgment, fun (a, _, b) => (a, b)⟩
def presentationAt (bytes : ByteArray) (offset : Nat) : SOS.Presentation :=
  ⟨shape, {r | r.premises = [] ∧ OutcomeAt bytes offset r.conclusion.1 r.conclusion.2}⟩

abbrev presentation (bytes : ByteArray) := presentationAt bytes 0

abbrev EdgeAt (bytes : ByteArray) (offset : Nat) (a b : State) :=
  (presentationAt bytes offset).Derives (a, b)

abbrev Edge (bytes : ByteArray) := EdgeAt bytes 0
abbrev RunsAt (bytes : ByteArray) (offset : Nat) := Relation.ReflTransGen (EdgeAt bytes offset)
abbrev Runs (bytes : ByteArray) := RunsAt bytes 0

def Admitted (bytes : ByteArray) : State → Prop
  | .written out => out.size = bytes.size
  | _ => True

end Silmaril.Wasm.Institution.Operational.MemoryWrite
