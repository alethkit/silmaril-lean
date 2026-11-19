# JSON object naming, profile SJ/1

[`JsonObject`](../Silmaril/Formats/Dasl/JsonObject/Defs.lean) adds a separate
wire profile to the [artifact naming prototype](artifact-naming.md). It is
not JCS, ATProto record validation, or an encoding of the RFC 8259 concrete
syntax. It uses the existing JSON wire reader/printer and DRISL model,
including the [JSON byte-roundtrip](https://github.com/hiloopai/silmaril-lean/pull/1135)
and the [canonical CBOR roundtrip](https://github.com/hiloopai/silmaril-lean/pull/1139).
The [debug JSON layer](drisl-debug.md) is separate: its `$bytes`/`$link`
wrappers are **ordinary property names** in SJ/1, not reserved syntax.

## Supported data and equality

The raw RFC grammar accepts ordered, duplicate object members and lone
surrogate escapes. `JsonWire.parseCst?` is the layer for trivia and original
token spellings. SJ/1 instead starts with a top-level object, sorts member
names recursively by UTF-16 code units, rejects duplicate names (even if
their escape spellings differ), and retains array order. The semantic object
type is the recursively strictly key-ordered representative. Strings and
keys retain **all** UTF-16 units, including lone surrogates, with no Unicode
normalization. The versioned body must fit CBOR's definite-length byte-string
size (strictly less than `2^64`).

Number equality is equality of the decimal `(sign, coefficient, exponent)`
triple, including negative zero, not equality of numerical values or rounding
to binary64. Thus `1` and `1.0` are different profile values, whereas `1` and
`1e+0` are the same. Raw whitespace, escape spellings, and numeral spellings
that parse to the same triple are not part of the claimed type.

## Encoding and the name theorem

The canonical block is a DRISL byte string containing `53 4a 01` (`SJ`,
version 1) followed by the deterministic UTF-8 JSON printing of that
representative. The envelope avoids interpreting non-scalar UTF-16 as CBOR
text or rounding decimal fields into DRISL numbers. It is an application-level
tag inside bytes, not a new CBOR tag, CID codec, or reserved JSON field. The
decoder checks the envelope, bounds, recursive key order and re-encoding;
alternate byte spellings are not accepted as canonical. `decode_encode`
proves recovery of every supported object, and `encoded_eq_iff` proves exact
agreement between canonical byte equality and profile object equality.

Fix a `Profile` whose relation has a name for every byte string, has at most
one name for each byte string, and emits only DASL object CIDs. Then
`exactly_one_name` proves `∃! name, names profile name object` for each
supported object. It is not a theorem about arbitrary relations or sparse
tables: aliases and missing bindings break the assumptions. Equal objects
cannot receive different names under this profile; the converse holds under
binding of the byte relation as an explicit extra hypothesis (`names_binding`).
This is not a claim about injectivity or correctness of SHA-256. The test
roundtrips a nested object, measures exact decimal and string distinctions,
and exports its bytes for external naming:

```sh
lake build --wfail +Silmaril.Formats.Dasl.JsonObject.Thms
lake env lean -DwarningAsError=true --run tests/formats/ArtifactJsonObject.lean /tmp/sj1.cbor
python3 -I tools/artifact-naming/verify.py name dasl drisl sha256 /tmp/sj1.cbor
```

The fixture's externally computed binary CID in hex is
`01711220ba9005f15d8dda3a116ca26d06c152c5a85d544d91b997c77066d524637efb09`.
