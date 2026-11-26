# Scoped PEG diamonds to typed λSSA

`ScopedDiamond` takes a shared prefix and two independently scoped arms in
the existing `PEG.Simple.Code` builder. The prefix contains a Boolean guard.
Each arm can name prefix values and its own earlier emissions, and returns an
ordered tuple of the declared result sorts. References may repeat. The
`toPEG` construction emits one actual zero-loop `PEG.Graph`. It rebases the
false arm over the concatenated table without giving it access to the true
arm's slots, then emits one PEG φ per result position under the same guard.
`peg_wellFounded` discharges the guarded Figure 11 evaluator's demand premise.
[Adapter definitions](../../Silmaril/SSA/PEG/Bridge/LambdaSSA/Defs.lean) ·
[PEG builder](../../Silmaril/SSA/PEG/Simple/Graph.lean)

A typed global PEG reference guarantees a vertex's result sort, and a
topological order can guarantee acyclicity. Neither determines which branch
produced a value or whether that value is available at a predecessor. Here
both arm builders start at the same shared context, and each output tuple is
typed over its own final context. The adapter expects this construction
from scoped inputs. It does not discover diamonds, infer dominance, or
partition a pre-existing flat PEG table.

## Translation and observation

`lower` schedules each block using the existing PEG bridge's `Operation.eval`
for copy, primitive and value-select. Ordinary PEG sorts remain distinct
typed λSSA bases, including Bool and count. One extra instruction encodes
the shared Boolean guard as the sum of units used by λSSA case. It maps true
to the left injection and false to the right. The existing
`SeaOfNodes.Diamond.Arms.LambdaSSA` lowering emits an actual Isotope region
with entry dispatch, two producer blocks and a shared typed join. Only the
taken arm executes. Its jump to internal label two packs its output wires
in their declared order. The predecessor list is false then true, while
dispatch selects the true block at label zero or the false block at label
one. The existing occurrence-indexed `PhiView` latches from the selected
edge's environment, and the join returns the packet at external exit zero.
[Existing diamond lowering and edge transfer](../../Silmaril/SSA/SeaOfNodes/Diamond/Arms/LambdaSSA/Thms.lean)

- `ScopedDiamond.lower_hasType` checks the original ordered parameter types and one external exit with the packed result type.
- `ScopedDiamond.observe_diamond` identifies the defined Figure 11 root tuple with the selected predecessor's ordered result tuple.
- `ScopedDiamond.lower_eval_iff` characterizes every finite evaluation of the generated region under the induced instruction interpretation. It has exit zero, unchanged ambient state, and the product encoding of the PEG root tuple with every slot defined. Conversely, those conditions give an actual λSSA evaluation. The theorem accepts any well-foundedness witness for the same PEG.

The proof compares actual Figure 11 observations through
`Simple.Code.observe_toGraph`. A per-slot invariant relates the source
builder values to each scoped scheduled dataflow. The invariant keeps
every local value defined in a `TotalModel`. Figure 11 still collects
every primitive operand strictly and reads only the chosen operand of φ.
This lets internal φ labels in pure dataflow lower to value-selects, while
the outer join φs correspond to the taken edge only. The proof then applies
the existing λSSA finite-return theorem. Its domain is one outer diamond
and pure total acyclic computations within the three tables. Loops,
partial primitives, effects, traps, divergence, and general SSA control
reconstruction are outside the theorem.
[Preservation statements](../../Silmaril/SSA/PEG/Bridge/LambdaSSA/Thms.lean) ·
[Ordered PEG bridge](peg-ir-bridge.md)

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Bridge.LambdaSSA.Thms PEGCoreTests PEGIRBridgeTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGIRBridge.lean
for module in \
  Silmaril.SSA.PEG.Bridge.LambdaSSA.Defs \
  Silmaril.Proofs.SSA.PEG.Bridge.LambdaSSA.Source \
  Silmaril.Proofs.SSA.PEG.Bridge.LambdaSSA.Correctness \
  Silmaril.SSA.PEG.Bridge.LambdaSSA.Thms tests.ssa.PEGIRBridge; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The regression exercises both branches with a computed predicate, distinct
arm computations, a mixed-sort join packet, a repeated result and a shared
operand. It checks predecessor occurrence identity, rejects an out-of-scope
arm reference, and rules out the internal join label and a changed state as
external observations.
[Regression](../../tests/ssa/PEGIRBridge.lean)
