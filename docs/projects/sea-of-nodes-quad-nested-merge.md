# A nested quad split with three incoming merge occurrences

Cliff Click's *From Quads to Graphs* §3.1 describes inspecting the
current definitions on every parsed path in nested if/then/else
structures before inserting Φ instructions at the merge. Figure 6
shows how each write updates the current-definition map. The source
is Rice TR CRPC-TR93366-S (October 18, 1993), SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[Archived manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

`Quads.Loop.Tail.Nested.check` reads the original quad table. The outer
true edge enters a second split. The inner true, inner false and outer
false occurrences run along disjoint jump segments to one common merge,
in that column order. A direct edge contributes the split itself as
predecessor, with the definitions after its ordered quads. The merge
jumps to a distinct tested latch whose true edge feeds back to the
header and whose false edge returns. The discovered blocks must cover
the table exactly once. An inner edge that skips the common merge and
goes straight to the latch is refused.
[Checker](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Defs.lean)

`Program.incomingTransfer` compiles the ordered quads of each path into
its own typed reaching-version map. `Program.merge_bank` validates each
map's complete bank. `Program.run_to_merge` identifies the column read
by the source runner and charges each visited split and each block of
the selected segment, stopping before the merge body.
[Source theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Thms.lean)

`Nested.MLIR.CF.prune` uses the existing carried mask and checks that
the smaller header can reconstruct the full post-header bank.
`Nested.MLIR.CF.lower` reuses the typed CF emitter with both original
split IDs and all source terminators. Each merge edge supplies the
register bank from its own final versions. Only edges into the header
use the smaller bank. `from_header_eq_merge` relates execution of the
emitted path to resuming at the merge with the source-computed column.
`lower_run` preserves the return or exhaustion at source budget `n`
and CF budget `n + 1`. The extra visit executes the typed return label.
This profile carries the full bank at the common merge and has one
nested split and one checked backedge.
[CF theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MLIR/CF/Thms.lean)

Build the fixture with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs`.
Paste the following into `QuadNestedMerge.lean` and run
`lake env lean -DwarningAsError=true QuadNestedMerge.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example

#eval predecessors                 -- [3, 2, 4]
#eval incomingResults              -- [7, 6, 10]
#eval (runSource 14, runCF 15)      -- (some 16, some 16)
#eval (runSource 13, runCF 14)      -- (none, none)
```

The first two lines read the three columns from the same initial
header bank. Execution takes two feedback edges and visits the merge
from blocks 3, 2 and 4 with results 7, 8 and 16. The regression checks
the three emitted merge packets, both projected feedback frames, and
the refusal case. The overwritten predicate reduces the carried bank
from seven fields to six.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MLIR/CF/Regression.lean)

## Run the numbered γ/θ graph

`Nested.Numbered.lower` emits a carried θ with the same header
reconstruction certificate as CF. The outer γ's true region executes
the inner split's quads and contains a second numbered γ. A direct
inner edge forwards the post-inner bank. The outer false region
executes its own arm quads. Neither split duplicates the common merge
or the tested latch. `checkResult` certifies that the θ stopping packet
retains the source return slot.
[Numbered emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Defs.lean)

`merge_run` connects the actual numbered routes to the corresponding
`Program.incomingTransfer` column. The graph resolves names in each
region's typed scope and supplies the same bank as the source column's
whole-path scope. `activation_run` gives the original stop/restart tag
and the simultaneous projected feedback bank. `returns_iff` connects
finite source returns with finite θ returns in both directions.
[Numbered theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Thms.lean)

`Comparison.cf_returns_iff` compares the same typed input and
the same encoded result with a separate budget witness for each
target. `cf_at_activations` counts the visited source blocks on the
selected paths, plus one CF return visit. `cf_diverges_iff` compares
absence of a return at every finite budget.
[Comparison theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs`.
Paste the block into `QuadNestedNumbered.lean` and run
`lake env lean -DwarningAsError=true QuadNestedNumbered.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested

#eval Numbered.Example.incoming
#eval Numbered.Example.thetaArity
#eval (Numbered.Example.sourceBudget 3, MLIR.CF.Example.runCF 15, Numbered.Example.runRVSDG 3)
#eval (MLIR.CF.Example.runCF 14, Numbered.Example.runRVSDG 2)
```

The three γ probes return `[(3, some 7), (2, some 6), (4, some 10)]`.
The numbered θ carries six fields, down from the seven source registers.
Three activations take two feedback edges and return 16 at CF budget 15.
The last line shows bounded exhaustion in both targets.
[Numbered regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Regression.lean)
