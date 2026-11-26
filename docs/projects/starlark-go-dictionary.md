# Pinned-Go dictionary profiles

`Silmaril.Languages.Starlark.Lists.GoDictionary.Thms` exposes a separate
executable dictionary profile. `Bucket.empty` and `set` build an eight-slot
table with no deletion. `get` computes the query hash and selects the probe
candidates from the occupied slots. Keys and values use the existing heap
carriers. Tuple key fields must remain immutable for the lifetime of the
table. The resolved interpreter continues to use its canonical key cache.
[Definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Defs.lean) · [Canonical profile](starlark-lists.md#dictionary-membership-and-lookup-profiles)

## Hashing

Keys in this profile are `None`, Booleans, integers, binary64 values and
nested tuples of those values. The integer hash uses the low 32 bits of the
signed value in the int32 range and of the magnitude outside it. The
binary64 path reuses the exact decoder. It applies Go's signed int64
conversion in range and rational division outside that range. Go hashes
infinities and NaNs to one constant. Tuples mix the raw field hashes, with
all arithmetic in 32 bits. The table reserves zero only after the whole key
has been hashed. A heap-sized bound on tuple reads admits the finite acyclic
keys of this profile and terminates on a malformed graph.
[Pinned integer hash][int-hash] · [Pinned float conversion][float-int] · [Pinned float hash][float-hash] · [Pinned tuple mixer][tuple-hash]

`intHash_toNat` states the modular formula. `hashesAt_iff` connects
successful executable hashing to independent field and mixer rules,
including binary64 decoding. The fixtures compare 25 exact raw hash words
with pinned Go, including signed int32 boundaries, a large negative integer,
fractional and out-of-int64 floats, and two unequal deep tuple keys with the
same hash.
[Theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Checks.lean) · [Go oracle](../../scripts/starlark/go-dictionary/check.go)

## Slots and observations

The occupied suffix represents slots in ascending order. Insertion uses
the highest vacant slot. A probe compares only entries with the normalized
query hash, using the default depth for each reached key comparison.
`candidates_slots` identifies that traversal with filtering the physical
slots. `set_hit_slots` and `set_miss_slots` give the exact slot update after
a hit or a miss with room. A hit names a live row and replacement keeps its
key and hash. Iteration follows the reverse of occupied slot order, so
writing through an equivalent key preserves its displayed key and position.
A miss at capacity is a profile rejection. Go grows its table on that path.
[Pinned slot insertion][insert] · [Pinned lookup][lookup] · [Ordered agreement](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Thms.lean)

`looksUp_iff` proves exact raw lookup agreement with the independent hash
and ordered probe premises. Both `contains` and `equalWith` use that
lookup and observe a reached key-depth error as a miss. Excluded keys and
malformed model reads retain their errors. Outer dictionary equality checks
size and walks the left insertion order, passing the remaining depth to the
supplied value comparator. A deep key collision can produce a raw error
before the cyclic value is reached. The paired fixtures exercise this case.
[Pinned membership][membership] · [Pinned dictionary equality][equality] · [Lean fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Checks.lean)

## First rehash

`GoDictionary.Growth.Thms` exposes a separate table that starts at one
bucket and can grow to two. Go hashes the query, then scans the selected
primary bucket and its overflow links in ascending slot order. It compares
only matching full stored hashes. An error aborts the insertion, and a hit
updates only the value. A miss at eight entries requests the first grow. A
miss at thirteen entries in a two-bucket table requests a second grow in Go
and returns a capacity error in this profile. A hit can replace its value
at either threshold.
[Pinned insertion][insert] · [Pinned overload and rehash][grow]

The model derives each home chain from chronological entries. Rehash uses
the low bit of the stored hash for the new home. A new entry takes the last
vacant slot in the chain. When every slot is occupied, the first entry of a
new overflow block goes in slot zero. Subsequent entries fill that block's
suffix from the end. The profile's bound allows at most one overflow block
per home. `slots_wellFormed` proves the occupied-slot permutation and chain
size. The append theorems give the physical updates, and `candidates_slots`
proves that the probe consumes the matching occupied slots in order.
[Growth definitions](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Defs.lean) · [Growth theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Thms.lean)

Go reinserts in linked insertion order and recomputes each key's hash. For
every prefix of the eight original rows there is no overflow, and the
candidates for each full hash are the same indexed rows in reverse
chronological order at both widths. `reinserts_two` lifts a successful
stable-hash replay to the wider table, and `reinsert_run` relates those
steps to actual insertions. The model can therefore derive the new
placement directly from those stored rows. `lookup_grow` preserves the
entire raw lookup result across a split before the ninth row is appended.
`set_first_grow` gives the miss, split and retry result, and replacement
preserves each row's stored hash and key at the same chronological index.
These results concern the no-deletion layout and replay rules with stable
key reads. Go's mutable pointers are outside the model.
[Pinned rehash][grow] · [Growth theorems](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Thms.lean)

Both membership and outer equality use the grown table's lookup. Paired
Lean and Go controls exercise a reached key-depth error before growth and
after growth, where equality treats it as a miss before reaching a cyclic
value. Ordinary numeric keys check the low-bit split, collisions, and key
identity across float alias replacement and rehash. Oracle-only trace keys
observe the actual probe order and recomputation of the eight stored
hashes.
[Growth fixtures](../../Silmaril/Languages/Starlark/Lists/GoDictionary/Growth/Checks.lean) · [Go fixture](../../scripts/starlark/go-dictionary/check.go)

The profiles start empty and assume an unfrozen table without active
iterators and immutable tuple key fields. Further growth, deletion,
process-dependent string hashing, callable keys, recursive Go-profile
dictionary values, and resolved interpreter integration are outside this
slice.

## Reproduction

```sh
lake build --wfail +Silmaril.Languages.Starlark.Lists.GoDictionary.Checks \
  +Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Checks
fixture="$(pwd)/scripts/starlark/go-dictionary/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

[int-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/int.go#L183-L193
[float-int]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/int.go#L447-L462
[float-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L476-L491
[tuple-hash]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1186-L1199
[insert]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L78-L150
[grow]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L153-L175
[lookup]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L177-L201
[membership]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1030-L1048
[equality]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L921-L951
