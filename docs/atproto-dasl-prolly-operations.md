# Shared finite Prolly operations

`Silmaril.Semantics.Prolly.Operations.Thms` is the plain typed entry point. It
uses the existing `OrderedMap`, `Tree`, and `build`, without a DASL dependency
or a naming argument. `TypedMap` packages strict key order, valid separators,
nonempty branches and the width bound. A valid input need not have canonical
cuts. `TypedMap.combine` interprets both inputs and rebuilds the entire result
under the selected policy. The view/rebuild and commuting theorems describe
the operation extensionally; there is no incremental merge or locality bound.

`Silmaril.Semantics.OrderedMap.Operations.Thms` is enough for callers that need
only the finite carrier, including set operations (`Unit` payload). It
distinguishes domain subset from preservation of key/value pairs, and equates
cardinality with the size of the key domain. A combine visits the sorted union
of domains; shared keys alone call the overlap handler. The handler is a pure
`Except` function, and its first error stops evaluation. A successful `none`
drops a shared key. Left/right bias, rejection, and discard are ordinary
handlers. Discard means symmetric difference for union and an empty result
for intersection; rejection succeeds exactly for disjoint domains. Lookup
characterizes every output, and carrier recovery does not involve wire names.

The key type supplies its equality and order. In a later link-keyed profile
the default is identity of the typed name, not equality of decoded contents.
Two names for one payload are not automatically aliases in these operations.
Rekeying that identifies distinct names is not a transport of this algorithm:
it requires its own conflict and ordering policy. The generic carrier does
not establish nameless-to-named lifting, even if a key encoding emits a link.
