# BlobArena design

BlobArena gives immutable bytes stable local handles and can register those
handles by content address. Its initial Rust surface is synchronous and
exclusively mutable. The shared Covalence adapter is a separate consumer of
the storage core. The Lean model specifies the sequential transitions and
classifies their results.

## Handles, entries and capabilities

Use an opaque `BlobId` with a zero-based `u32` slot index in a single arena's
owner scope. The backing slot vector is `Vec<Option<Entry>>`. Allocate at the
old length using checked conversion to `u32`, followed by fallible capacity
reservation before any publication. All 2³² indices are representable, subject
to the host's vector and allocation limits. Report index exhaustion or host
capacity failure explicitly. Never truncate, wrap, compact, or put new entries
in tombstones. Removal clears exactly the given slot. A fresh index is greater
than every index previously issued by that owner. Cloning, reopening, or
rebuilding a vector must use a fresh owner if it starts a new ID lifetime.

The u32 indexes dense storage. Owner and kind may be carried in a brand or in
the enclosing token, outside the index. Check owner and kind before indexing
whenever tokens can cross arenas, including Python and erased Rust boundaries.
Keep a runtime owner tag where static branding cannot enforce this. An
out-of-range or tombstoned ID is stale. Export a CID or other typed content
address for persistence, transport, or joining across arena instances.

An entry is either anonymous immutable bytes or a registration carrying its
exact typed address. A group table keyed by the normalized byte address holds
its registered live indices and any verified binding. A registration carries
no evidence and may exist before bytes become available. A byte binding can
also exist with zero registered indices. The three binding modes are local
authoritative bytes, a verified resident copy of retained backing bytes, and an
exact backing reference with no resident copy. Anonymous bytes are local and
pinned until removal or successful naming. Empty bytes are a valid payload.

Keep ID-based access and edits in `Arena`. An unindexed arena can implement
that surface alone. Reuse a separate `Lookup<K>` for typed keys in other
arenas, including a parsed-object or path index with no CAS. BlobArena adds
a byte-address profile, registration, and CAS-like access. This is the intended
shape of the Rust API, using Covalence's owned immutable `Bytes`.

```rust
pub trait Arena {
    type BackendError;
    fn read(&self, id: BlobId) -> Result<Option<Bytes>, ReadError<Self::BackendError>>;
    fn read_mut(&mut self, id: BlobId) -> Result<Option<Bytes>, ReadError<Self::BackendError>> {
        self.read(id)
    }
    fn insert(&mut self, bytes: Bytes) -> Result<BlobId, EditError<Self::BackendError>>;
    fn remove(&mut self, id: BlobId) -> Result<(), EditError<Self::BackendError>>;
}

pub trait Lookup<K> {
    type Id;
    type Error;
    fn lookup(&self, key: &K) -> Result<Option<Self::Id>, Self::Error>;
    fn lookup_mut(&mut self, key: &K) -> Result<Option<Self::Id>, Self::Error> {
        self.lookup(key)
    }
}
```

`BackendError` is the error type returned by a provider; the provider is a
separate value and type parameter. Classify foreign/stale IDs, unsupported
schemes, bad claims, collisions, allocation failures, corrupt reads, lost
backing references and provider failures. Return owned `Bytes` for reads, so
a result survives later edits. An optional resident-only `resident_bytes`
borrows `&[u8]` for the current arena borrow and performs no I/O. Avoid a public
`Cell<'_, Obj>` or an escaping mutable payload. Refcounts or a packed internal
representation can make bytes cheap to share; the API does not promise that
`Option<Entry>` is packed, that vector addresses survive growth, or that
a copied slice incurs zero allocations.

Generalize `Id` and `Obj` once a parsed consumer needs the common surface.
Native parsed slots can stay nameless and editable under the older contract.
A generational dense alternative can reuse indices with checked owner, kind,
index and generation, and must refuse generation wrap. A network-assigned ID
would need a namespace, uniqueness, lifecycle and transport rules. Neither
identity scheme changes what a content address proves. See the existing
[foundation](arena-foundation.md) and [typed spaces](arena-tagged-spaces.md).

## Address identity and evidence

Preserve the caller's exact typed claim for export. Normalize for byte identity
using a domain, algorithm identifier (including digest length), and digest.
Supported CID codec labels on a raw-byte lane may share the same algorithm
and digest. This is the same multihash rule on that lane. The default `put`
computes the raw BLAKE3-256 CID; also recognize SHA2-256 CID claims for typed
reservation, checked import, and compatible backing reads. Validate algorithm,
length and domain before lookup or transport. Reject unsupported algorithms or
lengths explicitly, including when the requested algorithm has the same digest
width as a supported one. Within a configured profile, a supported key with
no bytes is an ordinary miss.

Native Git OIDs occupy a separate typed lane. Check the repository's selected
SHA-1 or SHA-256 algorithm and expected object kind against Git's exact
`"<kind> <decimal length>\0" ++ payload` preimage, using the canonical Git
kind spelling and payload length in bytes. Keep expected kind in the typed
claim. Object kind and the Git encoding domain must survive normalization
and verification. A raw CID hashed over payload bytes alone is a different
address. A Git-object CID can bridge the lanes only by an explicit checked
conversion that specifies the exact framed bytes and kind. Agreement of digest
bytes alone never authorizes that bridge. The existing Git views supply
typed lanes and collision laws. [Git arena](../git-arena.md)

A checked byte binding is immutable for its normalized key. A resident binding
holds immutable bytes and verified evidence, such as a Covalence `Fact<Cid>`
for the byte-CID lane. A claim can include a codec label. Checking the
multihash says nothing about codec validity, canonical encoding or decoded
schema. A parsed consumer needs a separate successful decode and any
kind/schema check. Two inputs can satisfy the same claim. Compare exact bytes
against an established binding before accepting a duplicate. A differing valid
preimage is a conflict and must leave the first binding intact. This rule
covers test collisions, weak hashes and untrusted remote responses. Keep the
checks even for BLAKE3 and SHA2-256. Distinct algorithms or domains remain
distinct groups, even for identical payloads. Callers that want both addresses
must compute or verify and admit each one independently. Storage sharing across
those groups is an optional optimization with independent evidence for each key.

Use the smallest live index in a group as its representative. Several slots
may retain the same exact address or different supported codec labels for the
same multihash. A representative is about registration and does not depend on
residency, recency, or how the bytes arrived. Removing it selects the next live
minimum. A live named slot's `address(id)` followed by `lookup(address)` returns
its group's representative, which may be another slot. Re-export from that
representative can produce a different codec label on the same byte group.
A lazy anonymous insertion has no address until `ensure_address` succeeds.

## Operations

Inherent BlobArena methods use `insert(Bytes)` for a fresh slot,
`put(Bytes)` for address computation and block admission, and
`import_address(TypedAddress, Bytes)` for checked registration and byte
admission. Provide `insert_slice(&[u8])`, `put_slice(&[u8])` and
`import_address_slice(TypedAddress, &[u8])` under distinct names. A slice
helper copies if the borrow cannot provide immutable owned storage. Where a
verified input has a supported profile, a distinct `import_fact(Fact<Cid>)`
can reuse its claim and bytes after validating compatibility and the destination
binding. Keep owned methods explicit at the Covalence boundary.

| Operation | Preconditions and successful observation |
| --- | --- |
| `insert(bytes)` | With capacity, appends a fresh anonymous ID on every call, even for identical bytes. No hash, index binding or backing access is required. |
| `reserve_address(claim)` | With a supported claim and capacity, appends a new registered slot every time. Preserves the label. Performs no fetch, byte admission, hash check, or pin. An existing group binding is visible through the new slot. |
| `lookup(claim)` | Returns the minimum registered ID or `None`. Does no backing I/O. A miss says nothing about bytes. The mutable default delegates. A specialization may update lookup bookkeeping with the same result. |
| `address(id)` / `ensure_address(id)` | Read the stored claim or `None`; on an anonymous slot the mutable operation computes the default claim, verifies/adopts the binding, then registers the same ID. On a named slot it returns the existing claim, without certifying availability. |
| `read(id)` / `read_mut(id)` | Validate the handle. Anonymous bytes are directly available; named reads use the same checked byte path as `get`. An unbound registration with no backing bytes returns `None`. |
| `get(claim)` / `get_mut(claim)` | Resolve a supported address with or without registered slots. Prefer an admitted local or warm binding, otherwise fetch. A fetched block is verified before return or publication. Mutable reads can admit positive residency and touch recency. |
| `put(bytes)` | Compute and admit the default address. A repeated exact write is idempotent and returns that same address. It consumes no slot. It establishes availability in the arena's authority; it can use a matching retained backing binding. |
| `fill(id, bytes)` | Requires a live named slot. Check its claim and admit one group binding. All registered siblings see the result. Repeating an exact fill is a no-op. A mismatch against the claim rejects; a valid but distinct preimage conflicts. |
| `import_address(claim, bytes)` | Requires a supported claim, capacity, matching bytes and no conflicting binding. Acts as reserve plus fill in one commit. A duplicate exact import can return a new slot, with one group binding. |
| `remove(id)` | Tombstone the live slot and remove its registration, if any. A stale, foreign or wrong-kind ID fails. Removal leaves admitted blocks and backing untouched, even for the last slot. |
| `persist(claim)` | On an existing local binding, compare-and-admit exact bytes at the exact key via writable backing. Only successful retention lets it become a cold reloadable binding. Already anchored bindings succeed without another write. An unseen binding returns false. |
| `evict(claim)` | A warm reloadable binding becomes cold. A cold or missing binding needs no edit. Local authoritative bytes are pinned. Registration and exact binding identity survive. |

A verified backing miss for an unresolved registration is `Ok(None)`. A
missing previously retained block is a backing-loss error. Wrong bytes or
an unexpected claim from the provider are corruption. A provider timeout or
SQLite/transport failure is a backend error. Unsupported algorithms and bad
input claims have their own classifications. `&self` promises no arena warming
or touches; named reads can still do I/O and a provider may have its own
internal caching. Resident-only reads and registration lookup perform no
backing reads. By default `read_mut` and `get_mut` delegate. They can warm a
verified, reloadable value without changing registrations or admitted byte
identity. A warm hit can succeed while its backing is unavailable; the same
operation after eviction can expose that failure.

Python can expose a small named surface with opaque IDs, immutable `bytes`,
`None` for ordinary misses, and classified exceptions for other outcomes.

```python
a = arena.insert_bytes(b"data")
cid = arena.ensure_address(a)
b = arena.reserve_address(cid)
assert arena.lookup_address(cid) == a
arena.fill_bytes(b, b"data")
assert arena.read_bytes(b) == b"data"
assert arena.put_bytes(b"data") == cid
```

Additional helpers can be named `import_address_bytes`, `get_bytes` and
`get_bytes_warm`. A binding that crosses a language boundary is an immutable
snapshot, and its ID must retain its owner scope.

## Backing, policy and commits

Give `BlobArena<P, B>` separate policy and backing parameters. A null
backing has a definitive miss and offers no retention or writes. A memory
backing can give exact retention and atomic same-key byte compare-and-admit.
A read-only or shared byte provider can serve reads, but only a provider with
a retention contract can be used to drop a verified local payload. A positive
read from a volatile source can be returned after checking; keeping it as
authority through admission pins a local copy. A provider may expose a cheap
`has`, but existence cannot serve as a witness, and unsupported capability
or failure cannot serve as absence. The checked default for existence can
fetch and test for bytes. This is distinct from Covalence's unchecked `Cas::has`.

The default policy can be a zero-sized no-warm policy with static dispatch,
and null backing can compile down to the absent path. Explicit `persist` is
the first write policy. Automatic write-through is a future mode requiring
an exact retained write, and write-back would need a pinned dirty state and
explicit flush semantics. Residency planning can choose I/O-free reads at the
call site or skip warming; it cannot change a missing, corrupt or unsupported
result into valid bytes. A bounded LRU policy can touch only warm admissions
and hits on mutable paths, select oldest eligible victims, and account for
verified bytes once per retained group, across all group member slots. Use
checked sums. The cache budget excludes pinned local/anonymous bytes, entry
metadata, overhead and caller-held `Bytes` clones. If enforcing a whole-arena
memory budget later, charge pinned storage separately and reject before commit
when it cannot fit. A cache-only budget may decline warming and still return
the original verified answer. With no reloadable victims, a failed optional
admission makes no cache edit. Erased storage can use `Box<dyn BlobOps>`
with fixed ID, address and error types, owned results and an explicit subset of
insert, read, lookup, reserve/fill/import, get and put. It should not expose
concrete policy state, provider internals, generic typed operations or borrowed
resident bytes. Erasure alone adds no sharing or async guarantees.

Check handles, capacity, normalized keys, verification, and exact equality
before publishing. With no established binding, a matching retained backing
read may supply the exact anchor. A different verified block conflicts and
an unsuccessful provider read aborts admission. If the backing reports absence,
admit local authoritative bytes. When independently writable backing can race
with that absence, the local binding is authoritative inside this overlay.
Persist must compare-and-admit and can subsequently report a conflict. A
unified cross-client authority requires a single writer or atomic exact
compare-and-admit before publication. A provider's exact anchor must either
carry a stable identity with an exact immutable read contract or be checked
against retained evidence. Evicting weak-scheme bytes and later rechecking
only their hash is insufficient. Use a trustworthy immutable snapshot or
keep exact evidence where collisions are a concern.

Publish slot, membership, binding, and cache bookkeeping together. The core
validates any policy-proposed victim as reloadable and checks budget and
bookkeeping before publishing; a policy receives no unchecked mutation path.
Preflight all fallible local work before a durable write; use a backing
transaction where promises include coordinated durability. If successful
external CAS admission can outlive a failed local commit, such an adapter may
promise atomic local observations with possible unreferenced external blocks.
State that weaker contract explicitly. A transport error with uncertain write
outcome leaves local bytes pinned and any retry must be safe with exact
compare-and-admit. The model's pure error returns no successor. This describes
local rollback; physical I/O and crash behavior require separate contracts.

## Covalence and the shared variant

The public reference here is Covalence 0.1.0-dev.12 at
`5890a5fba9f76a850705abe40048f50f0b2541cf`.

- `Get<K: Key = Cid>` requires `get_unchecked(&self, &K)` returning
  `Result<Option<Bytes>, cas::Error>`. `get` defaults to that method. Override
  it or use the same checked path for both in this adapter. `Key` is a
  cloneable `Claim` with the CID crate's error type, platform bounds, and
  multihash comparison and relabeling. `GetExt::get_fact` checks the returned
  `Fact<K>` has the requested multihash and relabels to exactly the requested
  key. Its default fact source verifies returned bytes via `Fact::new`; a
  store can provide an already verified fact. Ranges, sizes and `has` do not
  verify a block. [CAS traits](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/trait/src/lib.rs)
- `Put<K = Cid>::put(&self, Bytes)` returns the store-selected `K`.
  `put_fact(Fact<K>)` must return what `put` would return, which can use a
  different codec or hash than the input fact. It does not promise arbitrary
  exact-key admission. Do not use it as `putExact` unless the adapter proves
  that the returned and served key satisfies the requested binding and
  provides the exact no-overwrite property. `Claim::check`, `Fact::new` and
  `Fact::of` provide evidence for bytes and the hash claim; a relabel does not
  validate a codec. [CAS traits](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/trait/src/lib.rs) · [Claim and Fact](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lib/cid/src/fact.rs)
- `MemoryCas` wraps a private `RwLock<Table>`; `Table` stores
  `Vec<Fact<Blake3>>` with a `HashTable<u32>` index. It implements both the CID
  and typed BLAKE3 lanes, strips the codec for BLAKE3 queries, returns a miss
  for other CIDs, and recalculates the raw BLAKE3 key when given a different
  hash. Its insertion skips a digest already present and panics on index
  exhaustion. Reuse the representation pattern in a new adapter with checked
  capacity and exact byte conflict checks. No changes to Covalence are needed.
  [MemoryCas and Table](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/memory/src/lib.rs)

The mutable arena exposes inherent CAS-like methods with exclusive mutation.
Covalence's `Put<K>` has a shared receiver and needs synchronized writes. An immutable or read-only
wrapper can offer `Get<K>` and eventually `AsyncGet<K>`. A read-only backing is
also compatible with a shared CAS whose local overlay is writable and pinned.
Full `Cas` requires all of `Get<Cid>`, `Put<Cid>`, `AsyncGet<Cid>` and
`AsyncPut<Cid>`, with Covalence's platform-specific send/sync bounds. The
shared adapter can also offer `Get<Blake3>` / `Put<Blake3>` if it provides
those typed operations independently. A native Git claim is not implicitly a
Covalence `Key`. Map arena failures to the available Covalence error variants,
preserving the underlying cause when boxed. Unsupported address configurations
and known corruption should never become successful misses. A backing adapter
must check its provider's supported lanes before interpreting `None`.

Start shared mode with `SharedBlobArena` over an in-memory table and a
non-warming shared read path. Use a lock for the short index and binding
linearization points and return owned immutable bytes/facts. Compute hashes
and do backing I/O outside locks. Take a binding snapshot, fetch and verify,
then recheck binding, ownership and current policy metadata before publishing
under a write guard. If the binding changed, reuse a matching winner or
retry/classify the conflict; a delayed fetch must never revive a tombstone.
With remote/SQLite backing, use exact-key uniqueness and compare-and-admit
in a real write transaction. Use async provider operations or a blocking
worker for the async traits, never synchronous I/O on an async executor
thread. In-memory operations can use ready futures. An LRU in shared mode
requires synchronized touches/admission or shared reads configured to skip
warming. Cache and lock ordering, external coherence and failure semantics
are implementation obligations. An erased local arena supplies none of the
extra capabilities by itself.

## Relationship to the earlier Arena design

The [language handoff](arena-trait-language-handoff.md) and
[trait contracts](arena-traits.md) remain references for explicit-key parsed
arenas and checked publication. The first blob surface reuses their distinctions
as follows.

| Earlier operation or idea | BlobArena counterpart or destination |
| --- | --- |
| `Arena::read` with hole/reservation/residence, explicit-key `reserve` and `insert`, optional `Allocate::allocate` | ID-based read validates owner and lifetime; a missing payload remains observable. Fresh append is mandatory for insert or address reservation. Explicit-key edits remain in the earlier arena. |
| `NamedReserve::reserve_named` and `fulfill_named` | `reserve_address` assigns the fresh slot; `fill` uses the exact registered claim and is idempotent on identical bytes. Neither registration nor successful group lookup entails availability. |
| `MutableCas::get`, probe and raw `put` | Checked byte read reports absence, corruption and backing failure distinctly. Local `put` admits an address without allocating a slot. Shared `Put` follows Covalence's receiver and owned bytes. |
| `key_name`, `attachedKeys`, verified `attach` | `address` exports the full claim, `lookup` returns the group's live minimum, and group membership includes unresolved registrations. Exact byte evidence is separate. `ensure_address` performs default lazy attachment for an anonymous blob. |
| `insert_and_publish`, `replace`, `replace_and_attach` | `import_address` stages a checked exact-address insertion. Blob bytes are immutable. Plain and stable-key replacement remain useful for parsed arenas; a changed blob is a fresh slot and keeps old admitted byte bindings intact. |
| Separate or tagged spaces, checked parsed ingress, rooted collection, optional interning | Keep typed owner/kind checks, immutable byte bindings, separately checked decoding, atomic local publication and no reuse. Tagged storage, byte authority collection, parsed-object residency and interning that returns an existing ID remain separate options. |

A file-tree watcher can use a hash-only lane to report typed Git or raw
addresses without promising retained bytes. Its retained lane can freeze a
snapshot, import/verify the bytes, and optionally persist them. A changing
file path is neither an immutable binding nor a reload anchor; a reread needs
verification and may fail. Watcher behavior, file mutation and Git wire
conversion are future work. For Prolly, retain the typed parsed block reader
and parameterized lookup from the earlier design. Local references may be
typed in-memory slots; encoded links and persisted roots carry CIDs.
Resolve and verify bytes and then decode the expected block schema. Range
routing, GC and rooted snapshot agreement remain in the existing reader and
collection contracts. [Prolly reads](arena-prolly-reads.md) · [Rooted surface](arena-prolly-rooted-surface.md)

## Checked model and implementation tests

The reference in `Silmaril.Semantics.Arena.Blob` uses an `Array (Option Entry)`,
a finite binding table, and an independently parameterized backing snapshot
with optional exact writes. Representative lookup scans the slots as the
specification of the production index. The oracle profile abstracts byte
verification and address selection. A cold witness is logical backing
evidence, excluded from resident accounting. The executable policy models
admission and a warm byte budget, with explicit eviction rather than an LRU.
It reuses the existing exclusive `Mutable.Mutation` commit operation.

Theorems cover append freshness and slot framing, representative selection,
binding admission and read verification, local pinning, and cache observation
under the stated backing conditions. Fixtures cover collisions and failed
publication as well as success. Run the targeted checks from the repository root.

```sh
lake build --wfail +Silmaril.Semantics.Arena.Blob.Thms +Silmaril.Semantics.Arena.Blob.Examples
```

For a Rust adapter, test u32 boundary conversion with a small injected
limit, tombstones and wrong owners, alias selection after removal, exact
duplicate and conflict behavior with a deliberate collision function,
and lazy address/lookup round trips. Add published BLAKE3-256 and SHA2-256
vectors, same-multihash codec aliases with invalid codec bytes, Git object
vectors for both repository algorithms and wrong kinds, and rejection of
unsupported lengths/algorithms and cross-domain reinterpretation. Exercise
absent, failing and corrupt providers, changed bytes under a weak hash after
eviction, cold/warm results, capacity and cache-budget independence,
uncertain writes and retries, and concurrent same-key publication against
a transactional backend. Lean checks the sequential byte-level model.
Cryptographic strength, Rust ownership and layout, concurrent refinement,
durability, and any Git or Prolly adapter implementation require separate
verification.
