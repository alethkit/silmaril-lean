# Ordered RVSDG lowering for Sea of Nodes memory

The lowering takes the admitted [straight-line memory graph](sea-of-nodes-memory.md)
and emits one RVSDG leaf per Load or Store in the source table order. Source
addresses and words become value ports. The single canonical runtime sort,
`.state PUnit.unit`, is interpreted as the whole finite heap. Start supplies
the heap after the scalar arguments, and Return emits the word followed by
the final heap.
[Lowering definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/RVSDG/Defs.lean) ·
[Ordered runtime interface](../../rvsdg/semantics/rvsdg-structured-runtime.md)

A source Load reads the current memory version and produces a word. Its
RVSDG leaf returns the observed word and forwards the identical heap on
a fresh runtime edge. The Store leaf returns the updated heap. The existing
`Checked` witness requires every target leaf and Return to consume the live
runtime origin. This retains the order between a Load and a later overwrite
even when the Load produces no source memory version.
[IR ’95 §2.5](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#one-memory-value)

`Graph.lower_returns_iff` compares the full typed target tuple with the source
return relation under the induced total leaf model. The regression returns
an earlier read of `11` after the same cell has been overwritten with `33`.
It inspects the target heap at both cells, including an unaffected cell
holding `7`. The theorem concerns one initialized heap and the specified
table schedule. Alias rewrites, multiple state components, branches, and
exceptions are outside the profile.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/RVSDG/Thms.lean) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/RVSDG/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.RVSDG.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.RVSDG.Regression
```
