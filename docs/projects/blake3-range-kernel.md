# BLAKE3 byte-range kernel

This is the foundation for proof decoders, not a Bao or Iroh wire-format
implementation. Import `Silmaril.Crypto.Blake3.Range.Check.Defs` for the
reference checker or `Silmaril.Crypto.Blake3.Range.Thms` for the judgments.

## Facts and trust boundary

- `Naming.ByteRange.Slice` and `Partial` are hash-independent. Given a whole
  named payload or an existing partial fact, checked subranges retain the same
  name and shift the byte offset. A `Partial` fact has a whole-payload witness.
- `Trace` is a compositional CV/ROOT relation. A leaf checks its exact chunk
  length and derives start/end flags and block boundaries. A parent uses the two
  child CVs in order. `eval_graph` is exact for the graph of a partial function;
  `eval_sound` and `root_sound` also allow a partial backend that is merely
  consistent with the relation. Output canonicity transfers from compression to
  traces and is distinct from binding in the reverse direction.
- `Read` checks subtree-relative offsets. Joining disclosures requires a suffix
  ending at the left-child boundary and a prefix starting at the right-child
  boundary. `verifyRange?` checks a decoded opening against the requested digest
  and returns the exact-length byte list with a `Checked` derivation. The
  numerical bound is `offset + fragment.length ≤ size`. A zero-length read at
  EOF works when the pertinent leaf is disclosed; opaque nodes are not read.
- An opaque non-root CV is an expected commitment, not evidence that it has a
  preimage. `Refines` opens an opaque node against its already committed CV and
  shape; `Root.refine` preserves the root and `Read.refine` preserves earlier
  byte facts. `Checked` does not imply `Partial`. The CAS adapter
  `Store.blake3_range` uses an actual store hit and partial hash compatibility to
  supply the whole-payload reference; it does not change the existing CAS API.

## Agreement and collision scope

`Trace.agreeOrCollision` starts with two checked traces for the **same geometry,
root mode, and output**; `Root.agreeOrCollision` uses the same digest and
extent. A matching parent compression input fixes both child CVs. Within a
chunk the comparison proceeds backward from the final output through the block
chain. A matching block input at an aligned position fixes the bytes because
the extent fixes the unpadded length and little-endian word loading is
injective. If inputs differ at any compared step, that step supplies the two
distinct primitive inputs and their common observed output. Neither result
requires canonicity or an injective compression assumption. The witness is an
existential in Lean, not a runtime collision exporter or a computational
security bound. Opaque nodes contribute no byte equality.

`Checked.sliceOrCollision` specializes this to a verifier opening versus a
fully disclosed actual payload that names to the digest and whose actual length
equals the proof context's `size`. **The checker does not independently
authenticate a claimed extent.** For example, an opening of the first chunk of
a 1025-byte object can pass with a claim of 1026 bytes if the last chunk remains
opaque. The compared ROOT inputs can literally be the same, so this ambiguity
does not produce a compression collision. The regression checks this case. A
format must bring a trusted extent or prove its own length/EOF binding before
using the fixed-context result to make claims about the object's actual EOF.

## Concrete profile

The scalar model implements unkeyed BLAKE3 with a 32-byte digest. At a normal
chunk compression the counter is the geometry-derived chunk index; in the
final compression of a single-chunk root it is the output-block counter zero.
The empty message is a single zero-byte block with `CHUNK_START | CHUNK_END |
ROOT`. A parent input uses the IV, a 64-byte block in left-CV/right-CV word
order, counter zero and `PARENT`, with `ROOT` added only at the root. Earlier
blocks of a root chunk do not set `ROOT`. `compressWide` implements both
feed-forward halves; `compress32` takes words 0–7, and `digestBytes` serializes
them little-endian. This is both the chaining projection and the first 32 ROOT
output bytes, **on different inputs**. The concrete collision conclusion
equates this projection, not the full 64-byte output. It says nothing about
collision resistance. The model is checked against selected upstream vectors;
there is no refinement proof against an external C/Rust/SIMD implementation.
Keyed mode, key derivation, and longer XOF output are not modeled by the checker.

Sources (not vendored): [C2SP BLAKE3 specification, sections 2–4][spec],
SHA-256 `85c336e9900538e572333dd16ddde9f605c000ec8293001dd4c2642193b9c07e`;
[BLAKE3 1.8.2 upstream vectors][vectors], SHA-256
`dcb91ea8accc77e6d6e632af7cdc1a99a9f3ae78cf648da595c7d064db32f624`.
The regression uses the upstream input pattern `byte[i] = i mod 251`.

## Decoder follow-up

Bao outboard, Bao streaming, and Iroh should refine their respective decoded
events to this kernel, rather than requiring a new hash argument per format.
State should carry the expected digest, extent policy, byte cursor, and
authenticated CV frontier indexed by canonical subtree geometry. Check length
arithmetic, wire framing, node order, truncation, trailing data, and the format's
completion policy separately. A staged fragment may be released only once its
local trace has a verified path to the expected root; receiving a CV or a
length field alone is not that check. No streaming transition, buffering bound,
or parser proof is supplied here. `verifyRange?` is a reference batch evaluator:
it builds an eager shape, so choose a resource-appropriate extent cap before
using it and separately bound parsing, disclosure size and buffering. A future
streaming engine should validate geometry on demand instead of allocating the
whole shape for a sparse opening.

```sh
lake build --wfail +Silmaril.Crypto.Blake3.Range.Check.Defs +Silmaril.Containers.Cas.Blake3.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/crypto/Blake3Range.lean
```

[spec]: https://github.com/C2SP/C2SP/blob/d35150e795e178b7ad26cdff0ec1877bcc9e9723/BLAKE3.md
[vectors]: https://github.com/BLAKE3-team/BLAKE3/blob/df610ddc3b93841ffc59a87e3da659a15910eb46/test_vectors/test_vectors.json
