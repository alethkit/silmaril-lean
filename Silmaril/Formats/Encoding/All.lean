module

public import Silmaril.Formats.Encoding.Relation
public import Silmaril.Formats.Encoding.Lattice
public import Silmaril.Formats.Encoding.Codec
public import Silmaril.Formats.Encoding.Per
public import Silmaril.Formats.Encoding.Category
public import Silmaril.Formats.Encoding.Fibration
public import Silmaril.Formats.Encoding.Encoded
public import Silmaril.Formats.Encoding.Carriers
public import Silmaril.Formats.Encoding.Unicode
public import Silmaril.Formats.Encoding.Base64
public import Silmaril.Formats.Encoding.Base32
public import Silmaril.Formats.Encoding.Base16
public import Silmaril.Formats.Encoding.Ascii
public import Silmaril.Formats.Encoding.Punycode
public import Silmaril.Formats.Encoding.Syntax
public import Silmaril.Formats.Encoding.FunctionalCat
public import Silmaril.Formats.Encoding.SyntaxCarriers

/-!
# Encoding theory

Encodings as values `EncRel σ α`, their lattice, induced partial
equivalences, categories `EncCat σ` / `EncCat₂`, encoded values, and carrier
functors (bytes, Unicode text, base64, base32, base16, naturals), and
text/binary syntaxes (`WithText`, `WithBinary`).  See `Silmaril.Encoding.Relation`.
Format instances live in `Silmaril.Formats.Json.Encoding`,
`Silmaril.Formats.Cbor.Encoding` and `Silmaril.Formats.Cbor.EncodingJson`
(and their `EncodingSyntax` companions).  `Silmaril.Encoding.Wasm` (`WasmText`,
`WasmBinary`) is not imported here, since it depends on the Wasm syntax.
-/
