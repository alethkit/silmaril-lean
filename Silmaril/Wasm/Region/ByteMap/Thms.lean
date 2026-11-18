module

public import Silmaril.Wasm.Region.ByteMap.Defs
import Silmaril.Proofs.Wasm.Region.ByteMap

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap
open Silmaril.Wasm.Binary.Core

/-- Source bytes encode the claimed instruction, including its actual prefix. -/
theorem span_sound {input : Input} {m : ByteMapEntry} (h : input.SpanChecks m) :
    input.DecodesAt m.decoded m.bytes := Proofs.span_sound h

/-- Executable validation, with proof fields erased at runtime. Invalid locals,
partial decodes, conflicting entries and nested paths fail closed. -/
def validate? (input : Input) (entries : List ByteMapEntry) : Option (Certified input) :=
  if body : input.BodyChecks then
    if table : input.TableChecks entries then some (Proofs.certify input entries body table)
    else none
  else none

/-- A successful result refers to the caller's exact table. -/
theorem validate_entries {input : Input} {entries : List ByteMapEntry} {result : Certified input}
    (h : validate? input entries = some result) : result.map.entries = entries := by
  unfold validate? at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  cases h
  rfl

end Silmaril.Wasm.Region.ByteMap
