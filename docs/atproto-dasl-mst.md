# ATProto MST node codec and local checker

This is the node format from the [ATProto repository specification](https://atproto.com/specs/repository#mst-structure), separate from Prolly. The
[codec](../Silmaril/Formats/Dasl/Mst/Thms.lean) uses exactly the `e` and `l`
node fields and the `k`, `p`, `t`, and `v` entry fields. `l` and `t` are
object links or null, and `v` is an object link to the record. `k` is an
inline byte suffix. `p` is nonnegative within the signed i64 profile. There
is no extra key, raw link, ignored field, or replacement on error.

Prefix lengths are maximal common byte-prefix lengths, starting at zero for
the first key. Compressing then expanding recovers the node; successful
expansion also recompresses to exactly the supplied compressed node. The
DASL encoder/decoder recover every successfully encoded node. These are
shallow-AST checks, not new canonical-CBOR roundtrip claims. Node bindings
are a relational pushforward of shallow object bindings; the partial
decoder preserves binding.

[Local validation](../Silmaril/Formats/Dasl/Mst/Defs.lean) checks nonempty keys in
strict unsigned byte order, exclusive context bounds, one layer for all entries,
no children at layer zero, and the empty-root/intermediate-node distinction.
The [ATProto specialization](../Silmaril/Formats/Dasl/Mst/Atproto/Thms.lean)
uses the repository SHA-256 and counts leading zero two-bit groups (at most
128). The generic local checker does not import the hash. Successful reads
carry local validity; missing inputs, invalid wire, and invalid nodes remain
different outcomes.

## Not Yet Checked

- Repository path grammar and record values are not validated by the node
  format. A valid local node does not imply it has a valid global completion.
- Define the finite tree interpretation and induced child intervals; prove
  strict interval partitioning, one-layer descent, no empty terminal child,
  deterministic canonical building, and map recovery.
- Prove a routed lookup sound for every binding extension with that tree
  interpretation. A null edge can certify absence only in a checked interval;
  a missing/malformed edge cannot. Keep updates and collision-safe publication
  under separate preservation theorems.

```sh
lake build --wfail +Silmaril.Formats.Dasl.Mst.Thms +Silmaril.Formats.Dasl.Mst.Atproto.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslMst.lean
```
