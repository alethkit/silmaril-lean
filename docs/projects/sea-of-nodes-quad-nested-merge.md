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
nested split and one checked backedge. Numbered γ/θ lowering of this
three-occurrence cyclic profile remains open.
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
