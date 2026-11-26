# SQLite structs in the object state store

Import `Silmaril.Machine.SQLite.GlobalState.StatePayload` to use the object
structs as the payload family of the state store.
[Object structs](object-structs.md) · [State store](global-object-state.md)

`IndexedStore.toObjects` produces `Objects TaggedId ObjectFields`. Each
object gets its kind from its tag and its fields from the corresponding
indexed map. A caller supplies `.live` or `.zombie` for each tag. This
assignment is consulted only for entries present in the struct store.
The bridge carries present snapshots. Allocation history, freshness and
lifecycle transitions stay in the state and resource layers.

`lookup_toObjects` checks exact preservation of the tag, state and typed
payload. `toObjects_toKinds` recovers the original kind erasure from this
payload-bearing snapshot. `toObjects_toStates_toKinds` specializes the
state store's `Objects.toKinds_map` law. It checks that dropping the fields
and then the state gives the same kind map as erasing the struct store
directly. The fixture includes a zombie connection and a live file with
the same numeric slot, and checks that an absent slot stays absent.

```sh
root=Silmaril.Machine.SQLite.GlobalState
lake build --wfail +"$root".StatePayloadChecks
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Machine/SQLite/GlobalState/StatePayloadChecks.lean
for part in StatePayload StatePayloadChecks; do
  SILMARIL_REPLAY_MODULE="$root.$part" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
make check CHECK_TARGETS=+"$root".StatePayloadChecks
```
