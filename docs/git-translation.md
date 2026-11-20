# Native Git to DASL name correspondence

[`Git.Translate`](../Silmaril/Formats/Git/Translate/Defs.lean) interprets a
finite, typed Git object unfolding twice. On the source side, the [native
profile](git-native.md) serializes the loose-object preimage, and its independent
assignment names those bytes. `NameBytes .sha1` and `.sha256` give the two
native OID widths; the library does not fix a hash implementation. On the
target side, the [DASL layout](git-dasl.md) and commit metadata codec produce
shallow object values and raw blobs. `Wire` separately specifies a possibly
partial object serializer and two byte-naming relations (object and raw).
For canonical ATProto DASL use `Formats.Dasl.Wire.Serializes`; `Wire.ofFunctions`
can instead state agreement with a supplied writer and byte-to-name functions.
The test uses native SHA-1 or SHA-256 and DASL CIDv1 with SHA-256.

`translate` takes an already typed `Object`, not a native OID or repository. It
computes child names before directories and tree/ordered parent names before
each commit. Shared occurrences are evaluated again rather than memoized;
`Audit.sharing` requires them to agree on the target for each `(kind, source)`.
Nothing requires distinct source names to get distinct target names. Prolly
blocks are in the target store and must satisfy the same byte-naming contract;
they do not represent native Git objects and do not get native-name pairs.

Reference cuts (ordinary subtree/parent refs or external gitlinks) are accepted
only when an explicit kind-aware frontier map supplies a target name; a missing
mapping rejects the fold. An accepted cut supplies no bytes or availability
evidence. `Trace.Closed` means no cuts, and `Audit.frontierAllowed` can instead
restrict permitted pairs for a partial view. The policy is by kind and name,
not by edge role; e.g. a commit OID allowed as a gitlink is also allowed as an
opaque parent. Use a closed unfolding when no cuts are permitted. The inductive
input rules out recursive structural cycles; an opaque reference can hide a
cycle, so a successful partial fold is not evidence of acyclicity.

## Checked claims

- `translate_native`: for any successfully translated finite unfolding, the
  independent native renderer yields the same root name. For an expanded object,
  its exact preimage is in the trace; for a reference, the trace records only
  its frontier pair. Changing the target layout or namer cannot change the
  source name or preimage if both translations succeed.
- `translate_commit_evidence`: for a successfully translated commit constructor
  with an `Audit`, its tree and ordered parents are paired with their translated
  names. The exact native commit preimage must occur at the source name in the
  caller's source observations and satisfy the native naming relation. The
  target codec recovers the mapped tree, ordered parents and selected metadata;
  the encoded commit is present in the target store with a serialization and
  target naming witness. `Audit.sameTarget` is the sharing guarantee for
  repeated same-kind names in that trace.

An `Audit` is supplied evidence, not an executable checker. Source-byte
agreement is separate from using a canonical target writer; no claim equates
the native and DASL digests, or says that the target metadata codec recovers
native bytes or fields it chose not to encode.

## Next slice: audited repository translation

1. Parse and validate the supported native preimages read from a store by OID;
   require the requested root OID and each discovered kind/name to match the
   parsed object and its original bytes.
2. Define reachability from that root and distinguish missing local edges from
   intentionally external gitlinks. Detect cycles on the active path; memoize
   completed objects by kind and native OID. Prove the result represents every
   reachable in-scope object, with only policy-allowed cuts on the boundary.
3. Check source/target block binding and materialize a target store, including
   Prolly internals. Prove the serializer, naming and sharing audit obligations
   for that traversal and the resulting repository-root correspondence.

## Checks

```sh
lake build --wfail +Silmaril.Formats.Git.Translate.Thms +Silmaril.Formats.Git.Native.Thms \
  +Silmaril.Formats.Git.Dasl.Layouts.Thms +Silmaril.Formats.Dasl.Wire.Defs \
  +Silmaril.Crypto.SHA1.Thms +Silmaril.Crypto.SHA256
lake env lean -DwarningAsError=true --run tests/formats/GitTranslate.lean
```
