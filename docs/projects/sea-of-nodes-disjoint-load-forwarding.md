# Load forwarding across certified disjoint Stores

IR ’95 §2.5 gives the whole-memory Store dependence and discusses
independence between writes. Simple chapter 10 folds a Load on a matching
Store and checks for conflicting writes in local memory transformations.
Here the initialized word-cell profile can establish independence by
comparing the actual cells supplied at typed address arguments.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Pinned Simple chapter 10](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations)

A certificate names the observed address argument and the address arguments
whose Stores may occur between the nominated Store and the selected Load.
`Certificate.check` checks each disequality on the concrete `Fin cells`
inputs. `Certificate.Valid` states the same obligation for a caller that
already has these facts. Port identity identifies which operations a fact
covers. Distinct address ports may denote the same cell.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Defs.lean)

The scan retains the nominated Store's value across covered Stores and
tracks its scalar origin across intervening Loads. The source Load still
observes the memory version produced after those Stores. The proof uses
`Heap.read_write_other` to carry the observed cell through each covered
write. The rewrite removes the designated Load and redirects every later
scalar use through the straight-line rewriter. All effects in the suffix
use the same table order and memory dependencies.
[Baseline forwarding](sea-of-nodes-load-forwarding.md) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Thms.lean)

`rewrite_returns_iff` preserves and reflects the returned word and entire
final heap for the checked input and any initial heap. For reuse across
inputs, `rewriteWith_denote` requires that each input satisfy
`Certificate.Valid`. The fixture forwards across an intervening Store,
uses the forwarded word in a later Store, and rejects both an uncovered
write and two address arguments naming the same cell.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Regression.lean)

The corresponding diamond check would carry and validate a separate
certificate and retained word for each Region occurrence.
[Joined forwarding](sea-of-nodes-memory-diamond-forwarding.md)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression
```
