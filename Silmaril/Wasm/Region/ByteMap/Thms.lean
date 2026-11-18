module

public import Silmaril.Wasm.Region.ByteMap.Defs
import Silmaril.Proofs.Wasm.Region.ByteMap

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap
open Silmaril.Wasm.Binary Silmaril.Wasm.Binary.Core

/-- Source bytes encode the claimed instruction, including its actual prefix. -/
theorem span_sound {input : Input} {m : ByteMapEntry} (h : input.SpanChecks m) :
    input.DecodesAt m.decoded m.bytes := Proofs.span_sound h

theorem locals_encoding (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) :
    Vec (Locals Forms.all) (input.bytes.take input.codeStart) (input.localGroups.map expandLocal) :=
  (Proofs.certify input entries body table).localsEncoding

theorem expression_encoding (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) :
    Binary.Core.Expr Forms.all (input.bytes.drop input.codeStart) input.body :=
  (Proofs.certify input entries body table).expressionEncoding

theorem body_encoding (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) :
    Binary.Core.Func Forms.all input.bytes (input.localGroups.flatMap expandLocal, input.body) :=
  (Proofs.certify input entries body table).bodyEncoding

/-- Data is constructed transparently; the private proof implementation only
supplies erased proof fields through the public theorems above. -/
def certify (input : Input) (entries : List ByteMapEntry)
    (body : input.BodyChecks) (table : input.TableChecks entries) : Certified input :=
  ⟨locals_encoding input entries body table, expression_encoding input entries body table,
    body_encoding input entries body table,
    ⟨entries, fun m hm => span_sound (table.1 m hm),
      fun m hm => ⟨(table.1 m hm).2.2.2.1, (table.1 m hm).2.2.2.2.1⟩,
      table.2.1, table.2.2⟩⟩

/-- Executable validation, with proof fields erased at runtime. Invalid locals,
partial decodes, conflicting entries and nested paths fail closed. -/
def validate? (input : Input) (entries : List ByteMapEntry) : Option (Certified input) :=
  if body : input.BodyChecks then
    if table : input.TableChecks entries then some (certify input entries body table)
    else none
  else none

/-- A successful result refers to the caller's exact table. -/
theorem validate_entries {input : Input} {entries : List ByteMapEntry} {result : Certified input}
    (h : validate? input entries = some result) : result.map.entries = entries := by
  unfold validate? at h
  split at h <;> try contradiction
  split at h <;> cases h; rfl

/-- Root coverage plus successful validation yields an actual grammar
certificate at every root position. Nested paths remain outside this result. -/
theorem root_coverage_sound {input : Input} {entries : List ByteMapEntry} {result : Certified input}
    (validated : validate? input entries = some result) (covered : input.RootCovered entries)
    (k : Fin input.body.length) : ∃ m ∈ result.map.entries,
      m.decoded = ⟨input.functionIndex, [], k.val⟩ ∧ input.DecodesAt m.decoded m.bytes := by
  obtain ⟨m, hm, he⟩ := covered k
  have member : m ∈ result.map.entries := by rw [validate_entries validated]; exact hm
  exact ⟨m, member, he, result.map.correct m member⟩

end Silmaril.Wasm.Region.ByteMap
