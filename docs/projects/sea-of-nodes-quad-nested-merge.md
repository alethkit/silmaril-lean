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

## Project the common merge bank

The join projection is separate from θ's carried-header projection.
Section 3.1 gathers changed definitions on all reaching paths. This
pass projects those columns when the merge replaces an incoming field
before any read. `MergePrune.mergeMask` uses the existing backward
producer sweep. `checkMask` validates typed renaming for every merge
producer and requires reconstruction of the **complete**
post-merge bank before entering the latch. This admits overwritten
inputs and keeps any unchanged slot that reaches the latch, even if
the merge itself never reads that slot. It is a conservative check
for this one merge.
[Projection certificate and reconstruction](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Thms.lean)

The numbered emitter removes the field from the outer γ's result
signature and from both of its output packets, preserving the original
nested γ and selection order. It uses in-scope header wires to fill
dropped inputs for the ordinary quad compiler. The certificate proves
those choices have no effect on the full reconstructed post-merge bank.
The typed CF emitter gives the original merge label the smaller block
signature. Every predecessor sends the same ordered projection of its
own final versions. The merge emits the certificate's renamed flow and
full outgoing bank. The original θ header projection is still applied
separately.
[Numbered proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Numbered/Thms.lean) ·
[Typed CF proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/MLIR/CF/Thms.lean)

`Numbered.merge_run` and `MLIR.CF.from_header_eq_merge` identify the
smaller bank at the selected source occurrence. Both targets preserve
their corresponding full-merge runner at every budget. The comparison
theorems transfer finite return witnesses across targets and compare
absence of a return at every finite budget.
[Comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs`.
Paste the block into `QuadNestedMergePrune.lean` and run
`lake env lean -DwarningAsError=true QuadNestedMergePrune.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example

#eval columns                          -- [(3, 41, some 7), (2, 42, some 6), (4, 43, some 10)]
#eval arities                          -- (6, some 6)
#eval refusesUsed                      -- (true, true)
#eval (runSource 14, runCF 15, runRVSDG 3)
#eval (runSource 13, runCF 14, runRVSDG 2)
```

Each row names the original predecessor, its distinct dead scratch
input, and the returned field from the actual reduced γ. Both emitted
join interfaces carry six of seven fields. The checker refuses to
drop the value read by the merge or the counter that crosses the
merge to the latch. Two feedback edges lead to a return of 16 in
all three runners, and the last line gives three exhausted runs.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Regression.lean)

## Drop inputs that survive the merge

Section 3.1 tracks the current definition at each incoming occurrence.
The merge–latch check starts with those definitions and follows the
ordered quads through the tested latch. `Latch.mergeMask` runs the
existing backward sweep over every producer. The final reads are the
resolved latch condition, return word and the actual θ-carried feedback
wires. `Latch.checkMask` validates those typed wires and all producer
operands. The pure profile retains every ordered producer.

`Latch.Checked.incoming_agrees` recovers that entire packet from the
smaller bank of any of the three occurrences. The complete post-merge
bank can differ. `Latch.Numbered.lower` emits the smaller outer γ and
reuses the original θ and arm routing. The checked packet proves that
the in-scope fillers for dropped wires have no effect on the branch,
return or retained feedback. The comparison reuses the existing
source and CF budgets, including absence of any finite return.
This comparison uses the full-merge CF emitter. The next section
gives the narrower CF emitter and its checked merge-to-latch edge.
[Certificate](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Thms.lean) ·
[Numbered emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Numbered/Thms.lean) ·
[CF comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs`.
Paste into `QuadMergeLatch.lean` and run
`lake env lean -DwarningAsError=true QuadMergeLatch.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example

#eval columns
#eval gammaArity
#eval overwriteAdmission
#eval refusesUsed
#eval tailPackets
#eval (runSource 14, runCF 15, runRVSDG 3)
#eval (runSource 13, runCF 14, runRVSDG 2)
```

The routes from blocks `[3, 2, 4]` bring decrement values
`[41, 42, 43]` and retained words `[7, 6, 10]` on the three
probe inputs. The common merge leaves the decrement unchanged.
The latch writes `255` before using or feeding it back. The emitted
γ carries five of seven fields. `overwriteAdmission` reports that
dropping only the decrement passes the packet check and fails the
complete-bank check. `refusesUsed` checks the merge operand, a latch
guard supplied by an incoming definition, a carried field used only
after feedback, and the original live latch counter. The successive
latch packets show two continuing activations and a stop returning
`16`. All three runners return `16` at budgets `14/15/3` and
exhaust at the smaller bounds.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Regression.lean)

## Emit the checked merge-to-latch interface in CF

`Latch.Split.prepare` starts with the shared merge–latch certificate.
The backward sweep on the separate latch keeps every producer operand,
the resolved guard and return word, and every field of the projected
header feedback. The checker then validates two typed transfers. The
merge sends just the needed latch inputs in register order. The latch
computes the same packet as the shared certificate. `Split.check` can
also validate a supplied latch mask.
[Checked interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Split/Thms.lean)

`Latch.MLIR.CF.lower` reuses the existing projected header and merge
labels and sends the original latch edges to its narrower block
signature. The wrapped label family retains a full-width latch label,
but all edges to the latch use the projected label. The additional cut
check can refuse a mask if either locally scoped transfer cannot be
renamed. `selected_predecessor_frame` identifies the actual emitted
incoming frame from each selected original predecessor. This includes
the inner split's direct edge and its post-inner definitions.
`merge_frame` gives the actual merge-to-latch arguments, and
`latch_frame` gives the selected exit word or simultaneous feedback
frame. The merge and latch still execute as separate source visits.
`lower_run` preserves the source budget `n` at CF budget `n + 1`,
including exhaustion. Only the final typed CF return adds a visit.
The comparison with the narrower numbered graph transfers finite
return witnesses at independent budgets and proves agreement when
neither runner returns at any finite budget.
[CF proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Thms.lean) ·
[Numbered comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs`.
Paste into `QuadMergeLatchCF.lean` and run
`lake env lean -DwarningAsError=true QuadMergeLatchCF.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch

#eval Example.columns
#eval MLIR.CF.Example.incomingArities
#eval MLIR.CF.Example.latchArity
#eval Example.refusesUsed
#eval (Example.runSource 14, MLIR.CF.Example.runCF 15, Example.runRVSDG 3)
#eval (Example.runSource 13, MLIR.CF.Example.runCF 14, Example.runRVSDG 2)
```

All three emitted merge edges and the subsequent latch edge carry five
of seven fields. The latch resets the dropped decrement to `255`.
The regression checks the exact emitted merge and latch packets on
both backedges and the exit, which returns `16`. It also checks the
merge operand, incoming latch guard, feedback field and counter refusals.
The interface covers the checked pure nested split, common merge and
tested latch.
[CF regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Regression.lean)
