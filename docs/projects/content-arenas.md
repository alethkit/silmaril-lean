# Content arenas: maps, trees and Git over one CAS

This is the design for typed Prolly maps and sets, a mutable Prolly arena, filesystem
tree snapshots and Git objects, all over one content-addressed store. It builds on
[BlobArena](blob-arena.md) and the checked [Git filesystem profile](../git-filesystem.md).

Status of each part:

- **Checked in Lean here:** hash-only naming equals persistent emission, and a
  retained subset of a tree answers soundly ([contract](#checked-contract)).
- **Read from source:** every statement about Covalence cites
  [0.1.0-dev.12](https://github.com/hiloopai/covalence/tree/5890a5fba9f76a850705abe40048f50f0b2541cf).
- **Proposed:** all Rust and Python signatures. None of them is implemented. The Rust
  blocks, concatenated in order, compile as a library with `rustc 1.100.0 -D warnings`
  once `dead_code` and `unused_variables` are allowed. Their bodies are placeholders.
  The Python block is illustrative and was not run.

## Layers

| Layer | Owns | Does not own |
| --- | --- | --- |
| Git objects and history | Git OIDs, commits, refs, shallow and promisor state | Tree layout, map chunking |
| Filesystem tree snapshot | Byte names, modes, one directory map per directory | History, OIDs, working-tree watching |
| Typed map and set | Key order, key and value codecs, a profile-tagged root | Node storage |
| Prolly arena | Local node slots, dirty nodes, path-copy edits, flush | Byte retention |
| BlobArena | Local blob IDs, verified address bindings, residency | Decoding |
| Store capabilities | `Resolve` and `Sink` over a backing CAS | Identity |

Each layer uses only the one below it. A tree snapshot and a Git history are different
things: a snapshot is a value with one canonical CID, and a history is a graph of
native objects with their own identities. Importing a Git tree as a snapshot needs no
commit, and reading a snapshot needs no OID.

## Identity

1. **Local IDs are typed and local.** A slot index is scoped to one arena owner and
   one kind. It is never encoded and never persisted. This is BlobArena's `BlobId`
   rule applied to node, tree and object slots.
2. **Portable addresses are immutable.** An address is a lane and a digest. A lane
   fixes the hash, the digest length and the preimage framing: raw bytes, DRISL
   bytes, or a Git object with its `kind SP length NUL` header. Encoded links and
   persisted roots carry addresses only.
3. **Verification is per lane and says nothing else.** Bytes are accepted for an
   address after hashing in that lane. Codec validity is a separate decode, and
   schema validity is a separate check.
4. **A collision is a conflict.** A second, different preimage for a bound address
   is rejected and the first binding stays. No operation here assumes a hash is
   injective, including the checked ones.
5. **A root is a function of its profile and its entries.** Edit order, batching
   and the store never change it. `Prolly.build_eq_of_lookup` states this for
   the model, and Covalence tests it as `canonical_whatever_the_history`.
6. **A bare CID is not a root.** A root is comparable only with its profile and
   schema. Persist the profile next to every root, because a small tree does not
   commit to its chunking parameters.
7. **Wire and tuning are separate types.** A `Profile` holds everything that can
   change a root: node layout, chunk rule and parameters, key codec, value codec,
   node hash. `Tuning` holds cache size, batching, parallelism, compression and
   retention. No tuning value may change a root or an answer.
8. **Retention never changes a name.** Hashing only, keeping a subset and keeping
   everything give the same root. Bytes that were not kept surface as a read
   fault and never as an absent entry.

```rust
use std::marker::PhantomData;

pub type Bytes = std::sync::Arc<[u8]>;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Lane { RawBlake3, DrislBlake3, RawSha256, DrislSha256, GitSha1, GitSha256 }
/// Portable and immutable: lane plus digest. The only identity that is ever encoded.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Address { pub lane: Lane, pub digest: [u8; 32], pub len: u8 }
/// Bytes already checked against `address` in its lane. Says nothing about codec or schema.
pub struct Fact { address: Address, bytes: Bytes }
/// Local, owner-scoped, never encoded, never persisted.
pub struct Id<Kind> { slot: u32, owner: u32, kind: PhantomData<Kind> }
```

`Lane` is closed on purpose. A Git lane address is not a DASL link: Covalence's
`Value::Link` holds only raw or DRISL CIDs with SHA-256 or BLAKE3
([value type](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lib/dasl/src/lib.rs)). A Git OID inside a DASL record is
therefore a byte string with its algorithm named by the record, and a generic link
walk does not follow it.

## Store capabilities

The question was whether one lookup with three outcomes should replace capability
traits. The answer is both, each for the part it fits.

- **Capability is static where it changes what code can exist.** A builder takes a
  `Sink` and no reader, so hashing a tree compiles and runs with no store. A reader
  takes `Resolve`. Lookup is optional because builders never ask for it.
- **Lane support is dynamic.** One erased store serves some lanes and not others,
  and an overlay asks several stores in turn. That needs a value, so `resolve`
  returns `Found`, `Miss` or `Unsupported`, and a failure is an error.

```rust
pub enum Lookup<T> { Found(T), Miss, Unsupported }
#[derive(Debug)]
pub enum StoreError { Corrupt(Address), Conflict(Address), Unauthorized, Io(std::io::Error) }

pub trait Resolve {
    /// `Miss` is authoritative for this store and lane. `Unsupported` says the
    /// store cannot index the lane. A failure is neither.
    fn resolve(&self, address: &Address) -> Result<Lookup<Fact>, StoreError>;
}
pub trait Sink {
    /// Offer one verified block. The sink may keep it, drop it, or record a promise.
    fn emit(&mut self, fact: Fact) -> Result<(), StoreError>;
}
/// Hash-only: every traversal runs, nothing is retained.
pub struct Discard;
impl Sink for Discard { fn emit(&mut self, _: Fact) -> Result<(), StoreError> { Ok(()) } }
```

The three outcomes must stay distinct because an overlay combines them differently.
`Found` returns. `Miss` and `Unsupported` continue to the next layer. An error stops,
since a later miss would otherwise be reported as authoritative. The overlay's result
is `Miss` only if some layer supports the lane.

Covalence does not make this distinction today. `MemoryCas`, `KvCas` and `SqliteCas`
return `Ok(None)` for a key in a hash they do not index
([KvCas](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/kv/src/lib.rs),
[MemoryCas](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/memory/src/lib.rs)), and `Error::Unsupported` names an
unsupported operation. The adapter over `Arc<dyn Cas>` therefore declares its lanes
at construction and checks the lane before it interprets `None`. It uses `get_fact`,
which always verifies. `Check` and `Mismatch` become `Corrupt`; `Backend` and `Io`
become `Io`. No change to Covalence is needed.

`Sink::emit` takes a verified fact, so a sink cannot be handed bytes under a wrong
name. Three sinks cover the cases: `Discard`, a retaining sink over `Put`, and a
filtering sink that keeps some lanes or addresses and records the rest as owed.

## DASL codecs

Covalence has `Value`, an event reader and a builder, and no `Encode` or `Decode`
traits ([crate](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lib/dasl/src/lib.rs)). Two traits are enough.

```rust
/// Everything that can change a root. Recorded next to every persisted root.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Profile { Legacy, V2 }
/// Nothing here can change a root or an answer.
pub struct Tuning { pub cache_bytes: usize, pub write_batch: usize }
```

```rust
pub struct Writer(Vec<u8>);
pub struct Reader<'a>(&'a [u8]);
#[derive(Debug)]
pub struct Malformed;
pub trait Encode { fn encode(&self, out: &mut Writer); }
pub trait Decode<'a>: Sized { fn decode(input: &mut Reader<'a>) -> Result<Self, Malformed>; }
/// Order-preserving and injective: `a < b` iff `key(a) < key(b)` bytewise.
pub trait Key: Ord + Sized {
    fn to_key(&self, out: &mut Vec<u8>);
    fn from_key(bytes: &[u8]) -> Result<Self, Malformed>;
}
impl Encode for i64 { fn encode(&self, out: &mut Writer) { todo!() } }
impl<'a> Decode<'a> for i64 { fn decode(input: &mut Reader<'a>) -> Result<Self, Malformed> { todo!() } }
impl Key for i64 {
    fn to_key(&self, out: &mut Vec<u8>) { out.extend_from_slice(&((*self as u64) ^ (1 << 63)).to_be_bytes()) }
    fn from_key(bytes: &[u8]) -> Result<Self, Malformed> {
        let raw: [u8; 8] = bytes.try_into().map_err(|_| Malformed)?;
        Ok((u64::from_be_bytes(raw) ^ (1 << 63)) as i64)
    }
}
```

The laws are `decode(encode(x)) = x` and, for accepted input,
`encode(decode(b)) = b`. The second is what makes equal values have equal CIDs. It
holds only for a strict decoder: one tag, no unknown fields, canonical DRISL.

**Links and bytes.** A link is CBOR tag 42 over a byte string of `0x00` followed by
the binary CIDv1. Bytes are a definite-length byte string. The JSON forms `$link`
and `$bytes` are for display and are never hashed.

**Derive or hand-write.** Hand-write the node and entry codecs. There are four of
them, they are frozen wire, and they sit on the hot path. A Serde bridge suits
application records instead. Serde's model has no link type, so links need a field
adapter. Map keys must be strings, and enum representation is chosen by attribute,
so a derive can change bytes without changing a type. Sorting keys canonically goes
through an intermediate value. Add a dedicated derive only when hand-written record
codecs become a maintenance cost, and pin every derived type with a byte vector.

**Typed keys.** Every key is a byte string on the wire, ordered bytewise with a
prefix first. A typed key is an order-preserving injection into bytes.

| Key type | Bytes | Why the order is preserved |
| --- | --- | --- |
| bytes | identity | by definition |
| string | UTF-8 | bytewise UTF-8 order is code point order |
| `i64` | 8 bytes big-endian with the sign bit flipped | maps the signed order onto the unsigned one |
| CID | binary CID | Covalence orders CIDs by binary form |

The kernel checker already keys by `u64` big-endian
([groups](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lean/kernel-checker/src/lean_check/groups.rs)), which agrees
with the `i64` rule on non-negative values. Tuples come later. They need a
self-delimiting encoding of each variable-length component, and that encoding is a
wire choice, so it belongs to a profile. A set is a map to the unit value.

## Prolly wire profiles

Three layouts exist. They are not interchangeable.

| Layout | Leaf and branch | Chunk rule | Where |
| --- | --- | --- | --- |
| Legacy | `{"$type": "vc.cov.prolly.leaf", "entries": [[key, value]]}` and `{"$type": "vc.cov.prolly.branch", "children": [[first_key, count, link]]}` | BLAKE3 of level and key, target 64, bounds 2 and 1024, fixed in code | [Covalence](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/prolly/src/node.rs) |
| Lean model | `["leaf", [[key, value]]]` and `["branch", level, [[max_key, link]]]` | Width 32, width-only, in the filesystem profile | [Prolly over DASL](../atproto-dasl-prolly.md) |
| V2 (proposed) | `{"l": [[key, value]]}` and `{"b": [[first_key, count, link]]}` | Named by the profile | here |

**Legacy is a frozen profile.** It is in production. The Lake cache builds a map per
revision, scans it and diffs it against its parent
([pool](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lean/cache/src/pool.rs)). The kernel checker scans and applies
sorted edits ([replay](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lean/kernel-checker/src/lean_check/replay.rs)),
and rebuilds a map to compare its root with a stored one
([receipt cache](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lean/kernel-checker/src/receipt_cache.rs)). Those roots
are persisted, so Legacy bytes must never change. One golden root pins the layout and
the chunk rule ([test](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/cas/prolly/tests/prolly.rs)):
`bafyr4idaucrnpulmucff2ca3xvtw6uj74fh24sp3fjzhlhyrgblcanwfku`.

**V2 is externally tagged.** A node is a one-entry map whose key is the variant.
The child tuple is unchanged from Legacy, so readers share all routing and count
logic. A decoder accepts exactly one key, `l` or `b`, and rejects anything else.
The header drops from 34 bytes to 3 on a leaf and from 37 to 3 on a branch. At 64
small entries per node that is about two percent, so size is not the reason to
adopt it. The reasons are a single discriminator, no field that can be omitted or
reordered, and the same shape Serde gives an externally tagged enum. Every wire
change forks every root. V2 should therefore ship once, together with any change
to the chunk rule and with parameters named by the profile, and only for new roots.

**A reader never guesses.** It is given the profile with the root and rejects a
node of another layout as malformed. A store may hold nodes of both profiles.

**The Lean model is not yet the Rust wire.** Its tag, separator, level field and
chunk rule all differ from Legacy. A theorem about the Lean profile is a contract
for the Rust code and is not a statement about Covalence bytes. Closing this gap is
the port item below.

## Prolly arena and typed maps

```rust
pub struct Node;
pub enum Child { Local(Id<Node>), Remote(Address) }
pub struct ProllyArena { profile: Profile, tuning: Tuning }
#[derive(Debug)]
pub enum MapError { Deferred(Address), Missing(Address), Malformed(Address), Stale, Store(StoreError) }

/// A persisted root. Two roots are comparable only at equal profile and schema.
pub struct Root<K, V> { pub profile: Profile, pub cid: Address, schema: PhantomData<(K, V)> }
/// An editable root inside one arena.
pub struct Map<K, V> { root: Id<Node>, schema: PhantomData<(K, V)> }
pub type Set<K> = Map<K, ()>;
pub enum Edit<K, V> { Put(K, V), Remove(K) }

impl ProllyArena {
    pub fn new(profile: Profile, tuning: Tuning) -> Self { Self { profile, tuning } }
    pub fn open<K: Key, V>(&mut self, root: &Root<K, V>) -> Result<Map<K, V>, MapError> { todo!() }
    pub fn empty<K: Key, V>(&mut self) -> Map<K, V> { todo!() }
    /// Reads fault in unloaded children through `store`; a miss there is `Missing`, never `None`.
    pub fn get<K: Key, V: for<'a> Decode<'a>>(&mut self, map: &Map<K, V>, key: &K, store: &dyn Resolve)
        -> Result<Option<V>, MapError> { todo!() }
    /// Path-copies in local slots. No hashing, encoding or store write.
    pub fn apply<K: Key, V: Encode>(&mut self, map: &Map<K, V>, edits: impl IntoIterator<Item = Edit<K, V>>,
        store: &dyn Resolve) -> Result<Map<K, V>, MapError> { todo!() }
    /// Encodes and names dirty nodes bottom-up, offering each to `sink` once.
    /// `Discard` gives the same root as a retaining sink.
    pub fn flush<K: Key, V>(&mut self, map: &Map<K, V>, sink: &mut dyn Sink) -> Result<Root<K, V>, MapError> { todo!() }
    /// Addresses a query would need and the arena lacks. Lets async callers fetch outside the borrow.
    pub fn wanted<K: Key, V>(&self, map: &Map<K, V>, key: &K) -> Vec<Address> { todo!() }
    pub fn admit(&mut self, fact: Fact) -> Result<(), MapError> { todo!() }
}
```

A persisted root and an editable map are different types. `Root` is portable and
carries its profile. `Map` is a slot in one arena and dies with it.

```rust
fn bump(arena: &mut ProllyArena, counts: &Root<i64, i64>, store: &dyn Resolve, sink: &mut dyn Sink)
    -> Result<Root<i64, i64>, MapError> {
    let map = arena.open(counts)?;
    let seen = arena.get(&map, &7, store)?.unwrap_or(0);
    let next = arena.apply(&map, [Edit::Put(7, seen + 1), Edit::Remove(-1)], store)?;
    arena.flush(&next, sink)
}
```

- **Edits are local.** `apply` path-copies into fresh slots and marks them dirty. It
  does not encode, hash or write. Only `flush` names nodes, bottom-up, and each dirty
  node is offered to the sink once. Intermediate versions that were never flushed
  never reach the store, which removes the garbage that one-put-per-insert creates.
- **Hash-only is a sink.** `flush` with `Discard` returns the root a retaining
  sink would return.
- **A miss below a root is a fault.** `get` returns `None` only when the loaded
  path proves the key absent. An unloaded child that the store lacks is `Missing`,
  and one recorded as owed is `Deferred`.
- **Borrowing.** Reads take `&mut self` so they can fault in nodes and touch the
  cache; results are owned. No reference into a slot escapes, so growth and
  collection cannot invalidate a caller's value.
- **Cache.** Clean nodes are a cache over the store and may be evicted at any time.
  Dirty nodes are pinned until flushed. The budget counts clean encoded bytes.
  Eviction cannot change an answer, only whether a read reaches the store.
- **Sharing.** An arena is single-owner. To share, flush and hand out the `Root`
  with a shared store; each thread opens its own arena.
- **Async.** The arena does no I/O of its own beyond `Resolve`. An async caller
  asks `wanted`, fetches outside the borrow, calls `admit`, and retries. This keeps
  the core free of async traits and works under WASM and Python.
- **Collection.** Local slots are collected from registered roots under the
  existing [rooted surface](arena-prolly-rooted-surface.md) contract.

## Filesystem tree snapshots

A directory is a map from a byte name to an entry. A tree is identified by the CID
of its root directory.

```rust
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Mode { Regular, Executable, Symlink, Directory, Gitlink }
pub struct Name(Vec<u8>); // non-empty, not "." or "..", no '/' or NUL
pub enum Target { Blob(Address), Tree(Address), Commit { algorithm: Lane, oid: [u8; 32], len: u8 } }
pub struct Entry { pub mode: Mode, pub target: Target }
pub struct Tree { arena: ProllyArena, root: Map<Vec<u8>, Vec<u8>> }
impl Tree {
    pub fn lookup(&mut self, path: &[Name], store: &dyn Resolve) -> Result<Option<Entry>, MapError> { todo!() }
    pub fn put(&mut self, path: &[Name], entry: Entry, store: &dyn Resolve) -> Result<(), MapError> { todo!() }
    pub fn remove(&mut self, path: &[Name], store: &dyn Resolve) -> Result<(), MapError> { todo!() }
    pub fn flush(&mut self, sink: &mut dyn Sink) -> Result<Address, MapError> { todo!() }
}
```

- **Names are bytes.** A component is non-empty, is not `.` or `..`, and contains
  no `/` or NUL. Other bytes are kept, including invalid UTF-8.
- **Modes are edge labels.** Regular, executable, symlink, directory and gitlink. A
  symlink is a blob holding its target bytes and is never followed.
- **A gitlink is a boundary.** Its target is an OID with a named algorithm and is
  not a link. Closure, retention and collection stop there. The checked profile
  rejects gitlinks today, and the first slice keeps that.
- **Empty directories are values.** The empty directory has a root like any other.
  Git's index does not record them, so a Git output codec must reject such a tree or
  be told to drop the directory. It never drops one silently, because that would
  give two snapshots one name.
- **Two names for one tree.** The canonical CID and a Git tree OID are different
  functions of the same snapshot. Neither is derivable from the other without the
  content. A correspondence between them is a map keyed by algorithm and OID, and
  admission compares on conflict.
- **Watching is later.** A watcher can report addresses on the hash-only lane. A
  path that can change is not a binding and is not a reload anchor.

The first object surface is small, and may live only in a Python wrapper that owns
the arena:

```python
root = Tree.scan("src").flush()            # hash-only: no store, nothing kept
tree = Tree.scan("src")
assert tree.flush(cas) == root             # same root when everything is kept
entry = tree.lookup(b"dir/\xff")           # Entry or None; Deferred and Missing raise
tree.put(b"dir/new", b"data", mode="regular")
```

### Retention

One traversal names a tree. A retention policy then decides which staged blocks are
kept. The policy sees addresses only.

| Lane | Keeps | Result |
| --- | --- | --- |
| Hash-only | nothing | the root |
| Partial | the blocks the policy accepts | the root, and a record of what is owed |
| Full | every block | the root, readable to every leaf |

Reading a partial store has four outcomes for a block, and only the first can
answer a query: found, deferred (owed by a recorded source), missing (not kept and
not owed), and invalid. A successful answer, including absence, equals the answer
of the full tree. This is the checked contract below.

## Git objects and history

Covalence has CID types for Git objects under SHA-1 and SHA-256
([git CIDs](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/lib/cid/src/git.rs)). At this revision it has no object
parser, pack reader, transport or reference store, and no store indexes SHA-1. The
contract below is what an importer must deliver. It assumes none of those parts.

```rust
pub struct Oid { pub algorithm: Lane, pub bytes: [u8; 32], pub len: u8 }
pub enum Filter { None, BlobNone, TreeDepth(u32) }
pub struct Request { pub wants: Vec<Oid>, pub depth: Option<u32>, pub filter: Filter }
pub struct Promise { pub source: String }
/// What an import delivered. `promised` and `shallow` are records, not evidence.
pub struct Imported {
    pub roots: Vec<Oid>,
    pub retained: u64,
    pub promised: Vec<(Oid, Promise)>,
    pub shallow: Vec<Oid>,
}
pub enum Parents { Known(Vec<Oid>), Shallow }
#[derive(Debug)]
pub enum GitError { Deferred(Address), Missing(Address), WrongKind, Collision(Address), Store(StoreError) }
pub trait Fetch { fn fetch(&mut self, request: &Request, sink: &mut dyn Sink) -> Result<Imported, GitError>; }
```

- **Namespaces.** An object's identity is its algorithm, kind and digest. It does
  not depend on which repository served it. Availability does: a promise names the
  source that owes the bytes, and a reference is an observation of one remote at
  one time. SHA-1 and SHA-256 names of one object are unrelated addresses.
- **Full import.** Every object reachable from the wanted roots through tree, parent
  and commit-tree edges is retained and verified. `promised` and `shallow` are empty.
- **Partial import.** Four different things can be missing, and they stay distinct.

| Case | Meaning | A read returns |
| --- | --- | --- |
| Filtered | The request excluded it, such as blobs or deep trees | `Deferred` |
| Promised | A named source owes it | `Deferred` |
| Shallow | A commit's parents were cut by depth | `Parents::Shallow` |
| Missing | Not retained and not owed | `Missing` |

- **A shallow commit still names its parents.** The commit bytes are verified and
  contain the parent OIDs. What is unknown is the parent objects. History queries
  report the boundary and never an empty parent list.
- **Merges.** A commit has an ordered list of parents. Traversal follows all of
  them, and depth is counted along each. Merging trees is a separate operation over
  two snapshots and is out of scope here.
- **Authentication.** Credentials belong to the `Fetch` value the caller supplies.
  They are never stored in an arena or a root. `Unauthorized` is a failure. It is
  never a miss and never a promise.
- **Resolving a reference.** A name resolves to an OID through a mutable, possibly
  authenticated lookup. Record the remote, name, OID and time as an observation.
  Covalence's `Kv` has no compare-and-swap ([Kv](https://github.com/hiloopai/covalence/blob/5890a5fba9f76a850705abe40048f50f0b2541cf/crates/kv/trait/src/lib.rs)),
  so atomic reference updates need a backend that provides one.
- **Collisions.** Two different objects under one OID conflict. The existing
  [collision policies](../git-oid-collision.md) apply unchanged.

## Workloads and gates

These are the workloads that exist today and the bound each must keep. Measure the
Legacy baseline first, on the same machine, and record it with the change.

| Workload | Shape today | Gate |
| --- | --- | --- |
| Lake revision map | Build once from sorted 16-hex keys, full scan, diff against parent | Root unchanged; node reads in a diff proportional to the change |
| Receipt map | Full scan, sorted edits, rebuild and compare root | Root unchanged; one flush per batch |
| Proof groups | `u64` keys, apply, point `get` on a history map | Same roots through the typed `i64` codec |
| Point edits at 100,000 entries | Covalence asserts at most 20 reads and 15 puts for three edits | No worse; zero blocks emitted before flush |
| Repeated single inserts | One stored path per insert | Blocks emitted equal the nodes of the final tree |
| Tree hash | Scan a directory, hash-only and retained | Equal roots; hash-only performs no store call |
| Partial Git import | Depth and blob filters | Every wanted object is retained or accounted as owed |

Compatibility gates, in the order they must pass:

1. The Legacy golden root is byte-identical.
2. Roots persisted by the Lake cache and the kernel checker open and scan.
3. Hash-only and retained builds agree on every fixture, for both profiles.
4. A reader given the wrong profile fails as malformed.
5. Lean-generated vectors and Rust agree on node bytes and roots.
6. No workload above regresses against its recorded baseline.

## Increments

1. **This change.** The checked retention contract and this design.
2. **First vertical slice.** `Profile` with Legacy only, `Sink` with `Discard`, and
   a builder that returns the same root with and without a store. Gates 1 to 3. No
   reader changes.
3. **Resolve.** The three-outcome lookup and the lane-checking adapter over
   `Arc<dyn Cas>`. Port the three consumers' reads without changing a root.
4. **Typed maps and sets.** `Key`, the codec traits, `Root` and `Map`. Port the
   kernel checker's keys.
5. **Mutable arena.** Local edits and `flush`. Port `apply` callers. The insert
   and point-edit gates.
6. **Lean profile for the Rust wire.** A `RootProfile` that produces Legacy bytes,
   with shared vectors. Then V2 as one new profile, for new roots only.
7. **Tree arena.** Directory maps, the Python wrapper, hash-only scan, retention.
8. **Git.** Tree-only import first. Objects, shallow and promisor state after the
   parser and transport exist.

## Checked contract

`Silmaril.Formats.Git.Filesystem.Retain` extends the tree-only filesystem profile.
The hash is an abstract function and no theorem assumes it is injective.

| Statement | Theorem |
| --- | --- |
| Hash-only naming equals the root of persistent emission, and fails with the same fault | `rootCid_eq_stage`, `directoryCid_eq_stageDirectory` |
| Keeping nothing leaves the store unchanged; keeping everything is publication | `Image.publishRetained_none`, `Image.publishRetained_all` |
| Every staged block is kept exactly or recorded as owed | `Image.accounted` |
| If the full closure is admitted, every retained subset is admitted and binds only its bytes | `Image.publishRetained_of_publish`, `Image.publishRetained_bindings` |
| A verified read from a partial store is the read from the full store | `readVerified_ofPartial` |
| A successful routed answer over a retained subset, including absence, is the source directory's answer | `lookupChildRouted_partial_sound` |
| A selected block that is owed and not kept is reported as deferred | `lookupChildRouted_deferred` |

The fixtures check equal roots on a nested tree with a non-UTF-8 name, an empty
directory and a symlink, equal faults on a gitlink and an invalid name, and a
33-entry directory with one leaf and the blob dropped.

```sh
lake build --wfail Silmaril.Formats.Git.Filesystem.Retain.Thms Silmaril.Formats.Git.Filesystem.Retain.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Git.Filesystem.Retain.Examples
```

Limits. The theorems cover the Lean block layout and the width-32 filesystem profile,
which are not Covalence's bytes. They cover one snapshot and a sequential store.
They do not cover commits, gitlinks, native OIDs, the mutable Prolly arena,
concurrency, durability or the strength of any hash. `promised` is a list the
importer wrote; nothing here proves that a source can deliver it.
