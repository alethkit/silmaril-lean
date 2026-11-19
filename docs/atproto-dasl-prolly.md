# Parameterized Prolly blocks over DASL

[The model](../Silmaril/Semantics/Prolly/Thms.lean) groups strictly ordered
entries bottom-up. A policy specifies a maximum width of at least two and a
level/key bucketer. There is no singleton cut; the last chunk may be short.
The builder stops as soon as the root fits. The checked results are lossless
flattening, common depth by construction, a width bound at every node, and
history independence for pointwise-equal finite maps. This is a worst-case
node-width guarantee, not a probabilistic balance or edit-cost result.

[The DASL adapter](../Silmaril/Formats/Dasl/Prolly/Thms.lean) instantiates keys
as byte strings in unsigned lexicographic order or signed 64-bit integers in
numeric order. With explicitly selected key and payload codecs, the profile
uses `["leaf", [[key, value], ...]]` and
`["branch", level, [[maximumChildKey, objectLink], ...]]`. Positive levels must
fit the signed profile; blob links are not valid child references. The
checked inverse is decode after successful encode, not an assertion about
all accepted syntax or canonical CBOR. This is not an ATProto MST format.

`Tree.observations` is the least relation of named blocks given a deterministic
bottom-up address function. `Stored` requires a successful shallow encoding
and the named binding at each block, not just compatibility with unrelated
observations. No hash injectivity is presumed. Equal semantic maps give the
same root name with the **same policy and fixed address function throughout**;
interchanging child names or choosing a different address can break this.
Raw-representation name uniqueness by itself is not this semantic guarantee.

[The closed-scan lookup](../Silmaril/Formats/Dasl/Prolly/Scan/Thms.lean) reads
all child occurrences with fuel. It checks declared levels, arity and width,
child separators, and strict key order across the concatenated leaf entries.
Missing data, invalid wire, invalid node, and fuel each give a distinct error;
only a completed scan can return absence. The proof relates every successful
answer to **any** binding reference containing the successful reads and the
canonical stored tree. It applies unchanged to such binding extensions.
The reader reuses the `Wire.ReadResult` interface; it does not reparse CBOR or
authenticate raw byte sources by itself. Local validation does not establish
canonical chunking for an arbitrary store. The theorem uses a canonical
reference witness; it does not assert every input has one.

[Routed lookup](../Silmaril/Formats/Dasl/Prolly/Route/Thms.lean) visits only
the first child whose inclusive upper bound covers the key. The builder
provably has strictly ordered leaf entries and truthful child maxima,
including on recursively lifted chunks. These global invariants justify
skipping siblings, even unreadable ones, and returning absence beyond the
last separator. A missing selected child is never absence. The checks on
the visited path do **not** certify an arbitrary root: negative and positive
soundness both require a rooted representation in the binding reference.
`routedLookup_build_sound` makes the two inclusion hypotheses explicit:
the reference must include the stored tree and the successful reader
observations. It does not need unique names.

`routedLookup_build_complete` proves the converse success guarantee given
`PathReads` and fuel strictly above the canonical root level. `PathReads`
requires exact decoded blocks on the selected path, not a fully readable
store. Going beyond the last separator needs only the current block.
`Stored.pathReads` supplies the premise for a shallow reader returning every
object binding of the store containing the tree.

## Follow-up

- Prove a declarative canonical-cut characterization, and derive exact path
  reads from a concrete canonical CBOR reader and stored-reference witness.
- Add update/admission proofs: successful updates preserve all old bindings,
  reject collisions, and do not rewrite missing or invalid blocks. Connect
  address derivation to a checked serializer and fixed hash on successful blocks.
- Model ATProto MST separately: SHA-256 two-bit-group layer rule, canonical
  longest prefix compression, exact `e` / `l` and `k` / `p` / `t` / `v` node
  shapes, and child intervals. A routed negative requires a valid interval and a
  checked terminal or absent edge; a missing child cannot certify absence.
