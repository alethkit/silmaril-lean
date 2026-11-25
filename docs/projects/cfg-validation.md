# Validation relations for forward λRTL CFGs

The validation relations use the existing `CFG.Block`, `CFG` and `Region` types.
At each sort, sets of ordered pairs form an inclusion lattice. The CFG levels are
`exactCFG ⊆ cfgIso view ⊆ close (cfgIso view)`. `cfgIso` renames all labels by a
single permutation, with no changes to register names, instruction order or
block order. The permutation must preserve `view` on every label. Each block
pair induced by a CFG isomorphism belongs to `blockIso`. `regionImage` transports
these inclusions to the image of the existing `CFG.toRegion` embedding.
[Forward CFG and dominator-tree semantics](ssa.md)

The one rewrite contracts an entry `br k x` into the first block `k(x)`.
Passing `x` to its own parameter leaves the store unchanged. The rewrite keeps
the block body and its ordered suffix. `contractEntry?` checks the jump target
and parameter. The checker refuses other entry shapes, including transfers that
would overwrite the parameter. `close` allows any finite chain of coherent
renamings and guarded contractions, including the empty chain.

`entryRelay_run` proves exact equality of the full results. Its proof uses the
existing `run_eq_toRegion` theorem, reduces the first `join` in the region, and
shows that the remaining `joinAll` preserves that equality. For every model of
a lawful monad and every input store, `close_run` proves equality after applying
`view` to the result label. Both sides retain the argument and every final
register. `region_satisfies` lifts this equality to the existing `rtlFullRoom`
judgment. This is the existing forward CFG semantics, in which jumps look up
labels only in the remaining suffix. The result is for that acyclic semantics
and the stated exit view. An external artifact's instruction semantics, loops,
and dominance-scoped SSA typing require separate evidence.

The examples check a label permutation followed by a contraction, reject a
permutation that changes the exit view, and compare two runs with identical
entry targets whose jump arguments differ. Changing the argument overwrites
the block parameter and changes the returned payload and store, so adjacency
alone cannot justify this contraction.

```sh
lake build --wfail +Silmaril.SSA.LambdaRTL.CFG.Validation.Examples.Thms
make check CHECK_TARGETS='+Silmaril.SSA.LambdaRTL.CFG.Validation.Examples.Thms'
```
