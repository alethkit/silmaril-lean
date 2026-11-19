# Abstract ATProto DASL and CAS

This layer models the signed ATProto core over [DRISL](https://dasl.ing/drisl.html)
and [DASL CID](https://dasl.ing/cid.html). It is not a Lexicon validator, a hash
implementation, or an implementation of the ATProto repository format.

## Contracts

| Header | Contract |
| --- | --- |
| [`Formats.Dasl`](../Silmaril/Formats/Dasl/Defs.lean) | One non-mutual indexed tree, with `Empty` ruling out edges and `Unit` erasing names. `Value.obj` and `Value.blob` expose nameless constructors. Dicts have a finite string key set, with one child per key; lists have one child per bounded index. Blob links are not inline bytes. |
| [`Formats.Dasl.Thms`](../Silmaril/Formats/Dasl/Thms.lean) | Shallow renaming respects identity and composition. `Extends` is a partial order preserving names, keys and lengths; it preserves shallow projection and only adds to the known bindings. |
| [`Semantics.Naming`](../Silmaril/Semantics/Naming/Thms.lean) | `Binding` is functionality by name. `UniqueNames` is functionality in reverse. Collisions are explicit; merging binding observations is associative, commutative and idempotent with a conflict top. Object serialization is a relational pushforward; determinism transfers binding, and a parser inverse recovers the source. |
| [`Containers.Cas.Naming`](../Silmaril/Containers/Cas/Naming/Thms.lean) | An opt-in adapter views the existing Docker/OCI store as the graph of its `Option` lookup. Its graph is binding whether or not its contents are sound. `Store.Sound` is graph compatibility with the hash; it does not imply hash injectivity. |
| [`Formats.Dasl.Wire`](../Silmaril/Formats/Dasl/Wire/Defs.lean) | `Drisl.parseCbor?` → ordered ATProto syntax → shallow tree. Rendering takes the reverse adapter and uses `Drisl.renderCbor?`, which sorts encoded keys. The parser rejects duplicate keys and noncanonical encodings before the abstraction drops order. The adapter validates the link tag against the DASL codec byte (`0x71` object, `0x55` raw). |
| [`Formats.Dasl.Resolve`](../Silmaril/Formats/Dasl/Resolve/Thms.lean) | A root name binds a shallow object, which may have many partial observations but at most one finite full expansion under binding (also after name erasure). The logical `fullLookup` does not promise executable termination. |

`Partial.links false` traverses inline dictionaries and lists and stops at object
and blob boundaries; `true` also traverses resolved object targets. Unresolved
links mention names but provide no bindings. The object witness for a resolved
link is its target's **shallow** projection. For example, the same object name
may appear twice, once with an unresolved blob inside and once with that blob's
bytes present: the two occurrences agree on the object binding. The regression
also exhibits two algorithm tags sharing one payload in a binding but
not-`UniqueNames` relation. Neither example assumes anything about real hashes.

`Partial.ConsistentWith` says the union of the store and observed bindings is
binding. It allows missing names but rejects incompatible *present* bindings.
`PartialNames` is stronger: the root and all known witnesses must already be in
the store. `Wire.readObject` preserves missing versus invalid wire (including a
wrong CID kind); it does not authenticate the contents by hashing. `Wire.Serializes`
is a checked relation: rendering emits the bytes and parsing recovers the given
abstract source. The checked relation is functional, but the foundation does
not claim every writer output satisfies the abstract roundtrip.

An `i64` leaf stores `UInt64` bits. The adapter uses `UInt64.toInt64` before the
existing signed wire encoder, which chooses CBOR unsigned or negative-integer
arguments from the signed mathematical integer. It reinterprets the decoded
`Int64` as bits, and `Wire.i64_roundtrip` proves this for every bit pattern at
the CBOR-number boundary. Byte regressions also cover both signed endpoints.

`completion_in_extension` gives a unique finite expansion when supplied with a
binding extension that preserves existing entries, contains the root, satisfies
`Closed`, and has an accessible dependency relation at that root. It does not
manufacture the extension or change the root's identity. `Closed` is a sufficient
condition on the whole supplied store, not a necessary condition for one root.
The extension cannot simply replace an existing malformed byte binding. An
unavailable required payload, a fixed cyclic binding, or a name for which no
supplied value meets the hash policy can prevent completion. None is filled
silently. `PartialOnly` requires at least one actual resolved link and no finite
full expansion; possessing only the shallow root is not enough.

## Remaining work

- [ ] **Canonical representation:** in `Wire`, prove both abstract roundtrips
  between canonical CBOR and key-extensional shallow trees. Use the existing
  DRISL correspondence and prove the key-permutation and array-index lemmas
  for this adapter. Keep debug JSON out of the byte-hash serialization path.
- [ ] **Partial resolution:** in `Resolve`, implement a fuel/policy-indexed
  deterministic observation and prove it satisfies `PartialNames`, preserves
  existing observations under increased fuel, and agrees with a finite expansion
  at sufficient fuel. Prove that every compatible partial observation refines
  into the full tree under binding, and characterize when a partial-only root has
  a nontrivial observation. The necessary and sufficient reachable closure and
  acyclicity conditions for full expansion are covered below.
- [ ] **Encodings and bounds:** add first-class total/partial encodings with
  recovery and bottom-up naming proofs (`UniqueNames` or fixed hash and a
  deterministic naming graph, not binding alone). Add association-pair and
  `{k,v}`-record map encodings, ordering/duplicate checks, and set encoding.
  Prove per-node and total bounds for inline structure, link depth and serialized
  bytes, distinguishing occurrences from distinct CAS names. Any probabilistic
  Prolly bound needs an explicit bucket distribution and assumptions.
- [ ] **Storage structures:** reuse the existing pure Prolly map checks and
  ATProto-style MST checks via separate DASL adapters. Prove the width/bucketer
  and canonical iteration invariants for byte/integer Prolly keys, and the
  ordering, SHA-256 layer rule, prefix compression and node-shape invariants for
  MST. Prove lookup and update soundness for all valid extensions, distinguishing
  unresolved, invalid wire, invalid node, verified absent and found. In
  particular, missing children must never imply absence.

## Checks

```sh
lake build --wfail Silmaril.Containers.Cas.Naming.Thms Silmaril.Formats.Dasl.Thms \
  Silmaril.Formats.Dasl.Resolve.Thms Silmaril.Formats.Dasl.Wire.Thms \
  Silmaril.Formats.Cbor.Drisl.Debug.Text.Thms Silmaril.Formats.Cbor.Drisl.Model.Thms
lake env lean -DwarningAsError=true --run tests/formats/Dasl.lean
lake env lean -DwarningAsError=true --run tests/formats/DrislDebug.lean
```

`make check` runs `DrislDebug.lean` when it builds `Silmaril`. Run `Dasl.lean` separately.

## Completing a raw store

`Silmaril.Formats.Dasl.RawStore.Thms` specializes a relational byte-store view to
the existing canonical CBOR parser. Object CIDs must decode; raw CIDs are leaves
whose bytes are not decoded. `full_exists_iff` requires a present, decoded root,
accessibility along object dependencies, and coverage of every direct link of
every reachable object. Under binding those conditions are also necessary. The
condition is local to the root, not global validity of all decoded objects.

`completion_iff` adds byte preservation, binding, and an explicit policy on
**all** retained/admitted bytes (e.g. that the supplied CID hash agrees).
`fill_completes` applies this criterion to supplied defaults, not a search for
them: `fill` tests absence in the original byte relation. In particular, present
malformed bytes cannot be replaced, a reachable cycle cannot have a finite
expansion, and rejected present bytes cannot belong to a policy-respecting
extension. Even when a name is missing, no claim is made that an allowed default
or hash preimage exists. The Docker opt-in adapter's `fillMissing` realizes the
same relational operation on its partial maps; `checked` and `decode` still
filter reads and are not used as tests for absence when filling.

Standalone countermodels: `lake env lean -DwarningAsError=true tests/formats/DaslRawStore.lean`.
