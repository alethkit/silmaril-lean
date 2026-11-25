# Tagged mathematical record sets

The value operation implements `[h₁ : S₁, …, hₙ : Sₙ]` as a set of graphs.
Every member has exactly the listed string keys, and its value at each key
belongs to that key's specified bound. Records share the same function
representation as other tagged graphs. Keys use `Value.string`, the existing
tuple-of-characters representation, with `Value.string_injective` for equality
of field names. [Specifying Systems §16.1.8, pp. 305–306](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=323)

| API | Contract |
| --- | --- |
| `SetData.recordSetKeys`, `SetData.mem_recordSetKeys`, `SetData.string_mem_recordSetKeys` | The domain contains exactly the existing string encodings of the listed field names. |
| `SetData.recordSet`, `SetData.mem_recordSet`, `Graph.fitsRecordSet` | Membership supplies the graph, its exact domain and a checked lookup with per-field membership for every listed bound. |
| `SetData.record_mem_recordSet`, `SetData.mem_recordSet_nil` | A conforming record body yields a member. A valid empty schema contains just the empty graph. |
| `Value.checkRecordSetFields`, `Value.recordSet` | Validate ordered field operands and produce the tagged set or the result of a fixed invalid-input policy. |
| `Value.checkRecordSetFields_encoded`, `Value.recordSet_valid`, `Value.recordSet_invalid`, `Value.recordSet_nil` | Equations for tagged set operands, successful validation, a reported error, and a valid empty schema. |

[Definitions](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Collections/RecordSet/Defs.lean) ·
[Laws](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Collections/RecordSet/Thms.lean) ·
[Checked examples](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Collections/RecordSet/Examples.lean)

The mathematical construction forms a function set on the finite key domain
with range bounded by the union of the supplied set payloads. Separation
enforces the per-field bounds. The bounds themselves can be empty or infinite.
The checked examples admit a graph-valued field whose exact domain is the
supplied participant set, including both the empty set and the integers. A
nonempty schema with an empty field bound yields an empty record set.

Source TLA+ requires distinct identifier labels. SANY checks duplicates in
both record forms. [Pinned SANY duplicate-field check](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Generator.java#L4092-L4123)

The typed operation
`SetData.recordSet` takes decoded set bounds and interprets repeated keys
conjunctively. The value-facing validator rejects duplicates before decoding
any bounds. With distinct labels, it reports the first non-set bound as
`.nonSetBound name`. The value entry accepts arbitrary Lean strings as keys,
so source spelling rules belong to source analysis. Its empty list is a
valid schema, a value-level case independent of the source grammar.

A caller supplies one `RecordSetFallback` for all evaluations. The fallback
receives the error and original operands and can return an arbitrary tagged
value. The validation result distinguishes the two malformed cases even if
the policy gives both the same value. A source evaluator still has to lower the
record-set form, preserve the label/operand pairing, and decide how to report
malformed source or domain-invalid operands. This operation supplies the
mathematical set and laws for that integration.
