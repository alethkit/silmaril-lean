# Name-ordered DASL link sets

Use [`NameLinkSet`](../Silmaril/Formats/Dasl/NameLinkSet/Defs.lean) as the
default linked collection when membership is by reference. `objectKey` and
`blobKey` use the caller's `LinearOrder` on names; `mixedKey` uses tagged names
(objects first, then blobs, each in name order). The generic `codec` accepts a
recovering key codec and checks that decoding retains the exact input links.
The shallow format is one array of links in strictly increasing key order.
Decoding needs no store. `normalize` sorts and deduplicates input keys;
decoding rejects unordered or duplicate entries rather than repairing them.

For DASL or BDASL, select `cidOrder` explicitly for unsigned lexicographic CID
bytes, and use `cidWireCodec` with the corresponding wire profile. It checks
the CID codec kind (`0x71` object, `0x55` raw blob) on write and read. A mixed
layout can distinguish two tags on the same abstract name only when its profile
permits it; the concrete CID guards are disjoint. Wire representation remains
partial and neither profile here verifies a digest or assumes that every
abstract name serializes. The order and key codec must be part of the agreed
layout, not inferred from the bytes.

`index` builds a sorted array once. Its binary search is proved equivalent to
name membership; each failed pivot discards a side and narrows the window to at
most half its width. This does not bound the cost of key comparison, decoding,
index construction, or block reads. `lookup` returns `none` for an unindexed
name. An indexed name can be unresolved (caller did not obtain a result),
missing (no bytes observed), invalid (wrong kind or ill-formed object), or
found. Blob bytes are not parsed as objects. Negative outcomes do not show
semantic absence. Positive wire reads are sound for every store relation that
contains the observed byte bindings; a binding store then gives a unique
decoded payload **per tagged name**.

The [theorems](../Silmaril/Formats/Dasl/NameLinkSet/Thms.lean) characterize
layouts as finite sets of keys and prove recovery, kind admission, exact link
identity and lookup soundness. `contents` is the relational image of the
members; multiple member names may resolve to the same payload. Name
cardinality does not count distinct contents. `ofContents` takes a caller's
total name selector, required to bind the requested values when interpreting
the result. Under that coherence and a binding relation the content view
recovers the input set, and layouts are canonical for that fixed selector and
order. This does not prove wire-encoding existence or choose a representative
for aliases. Two coherent selectors can produce different bytes for the same
content, even under one binding relation.

Choose the existing [content-ordered `LinkedSet`](atproto-dasl-linked-set.md)
explicitly when membership and deduplication must be by content. It resolves
links, checks canonical payload keys and enforces preferred links. The two
layouts may have identical array syntax but different semantics and ordering
rules; select the layout out of band, not by interpreting one as a fallback for
the other. The `LinkedSet` API and wire interpretation are unchanged.

```sh
lake build --wfail +Silmaril.Formats.Dasl.NameLinkSet.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslNameLinkSet.lean
```
