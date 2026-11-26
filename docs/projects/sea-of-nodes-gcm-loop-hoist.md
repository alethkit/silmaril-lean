# Hoisting an invariant producer to the existing preheader

Click's PLDI ’95 scheduling constraints place a producer after its inputs become
available and where it dominates its uses. Section 2.4 favors the shallowest
loop nest. This pass applies the checked natural-loop ranking to the typed CFG
emitted by the existing pure Sea of Nodes loop lowering. It then moves one
operation into that CFG's existing preheader.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Loop ranking][forest] ·
[Existing lowering][lower]

## First header binding

The source has a preheader, one header with a self-backedge, and an exit. The
pass inspects the first typed binding in the emitted header. Its operands refer
to the current latch word or captured function inputs. The corresponding
operand sites are header cut zero for the latch and preheader cut zero for
the captures. The pass tracks the producer's typed variable index through the
rest of the header. It records ordinary reads at local cuts and branch
arguments by exact successor slot and argument number.

`pickAndHoist?` calls `LoopForest.choosePlacement` with those sites on the
actual source CFG. The supported destination is preheader cut zero. A
structural capture check translates the producer operands into entry scope
and rejects any reference to the latch. A successful pass inserts the
producer there, keeps the existing preheader bindings in order, and removes
the original header binding. This follows the checked pick-and-emit pattern
used for the diamond hoist. [Definitions][defs] · [Diamond hoist][diamond]

The preheader passes the saved result before the original latch argument.
Every true header transfer sends that same result before the next latch
argument. The new header parameter occupies the old producer's lexical
position, so the remaining header bindings read the same values. The false
transfer sends the same result argument to the existing exit. [Definitions][defs]

## Nominated header binding

`pickBindingAndHoist?` takes a zero-based index into the same lowered header.
The traversal records where each typed variable comes from. At entry to the
header, the latch is local and the remaining variables are captured function
inputs. Each earlier binding extends the map with its own definition cut and
shifts all existing names. The ranker sees a local operand at its exact cut
and the selected binding's uses at their actual cuts and successor occurrences.

A nominated binding is movable when its operands read the immutable inputs
directly and the ranker chooses preheader cut zero. The rewrite copies the
earlier bindings in their original order, shifts their references to the new
scope, then substitutes the saved header argument for the selected binding.
The lowering's existing typed block and edge representations carry the result
through entry and feedback. [Definitions][defs]

`pickBindingAndHoist?_placement` certifies the nominated cut.
`pickBindingAndHoist?_routes` proves exact entry, feedback, and exit transfers
with the saved result computed from the captured operands. The proof matches
each earlier operation's typed operand values before substituting for the
nominated result. `pickBindingAndHoist?_run_eq`, `pickBindingAndHoist?_budget`,
and `pickBindingAndHoist?_returns_iff` carry these transfers through CF fuel,
native backedge budgets, and finite returns. [Theorem header][thms]

The later-binding regression moves the third binding past a latch-dependent
producer and a second producer that uses its result. Both earlier bindings
participate in the feedback calculation. The saved result remains `2` as the
latch advances `3 → 7 → 11`. Both CFGs agree at zero and two backedges. When the
third binding takes the second binding's result as an operand, the checker
reports header cut two as the operand site and rejects the preheader.
[Regression][regression]

## Adjacent invariant dependency slice

`pickSliceAndHoist?` nominates the consumer of two adjacent header bindings.
The consumer must read its immediate predecessor. The prerequisite's operand
origins must be captured inputs. The consumer may read that prerequisite and
captured inputs. Reads of the latch or other local results fail capture.
This check reuses the typed origin map from the single-binding pass.
[Definitions][defs]

The ranker checks each definition at preheader cut zero. For the prerequisite,
the use list includes the actual consumer read and any remaining local or
edge uses. For the consumer, the internal dependency becomes a preheader
operand site, and the remaining uses retain their source cut and occurrence.
The emitter enforces dependency order within the shared cut by binding the
prerequisite first, then evaluating the consumer in that extended scope.
Earlier bindings stay in their original header order. The entry and feedback
edges carry both saved results ahead of the original latch argument.
[Checked loop ranking][forest] · [Definitions][defs]

`pickSliceAndHoist?_placement` establishes legality for both site lists.
`pickSliceAndHoist?_routes` proves exact entry, feedback, and exit transfers
using the two saved values. Its proof follows the retained prefix, evaluates
the prerequisite on captured inputs, then checks the consumer with that value
in scope. `pickSliceAndHoist?_run_eq` preserves all CF fuel observations,
`pickSliceAndHoist?_budget` preserves the `k + 3` mapping, and
`pickSliceAndHoist?_returns_iff` preserves and reflects finite returns.
[Theorem header][thms]

The fixture keeps a latch-dependent binding in the header. The exit uses
the prerequisite and feedback uses the consumer. It checks that the
single-binding checker rejects the consumer at the preheader and that the
slice moves both definitions. Entry and two feedback transfers keep the
consumer and prerequisite at `3` and `2` as the latch advances from `3`
to `7` to `11`. The fixture also checks immediate exit and rejects a
prerequisite that reads the retained latch-dependent result.
[Regression][regression]

## Invariant pair across retained bindings

`pickSliceAcrossAndHoist?` takes the zero-based prerequisite index and the
number of retained bindings before the consumer. A gap of zero gives the
adjacent case. Each gap binding extends the source scope with a local
definition and shifts the typed reference to the prerequisite. The consumer
must read that exact reference. A missing binding, a missing dependency,
or an operand that reads the latch or a retained local result fails capture.

The scan checks all uses of the prerequisite, including reads by the
retained gap and exact successor operands. The ranker checks both moved
definitions at preheader cut zero. The emitter evaluates the prerequisite
before the consumer there and reuses both saved results in the header.
The gap bindings retain their order and can read the saved prerequisite
as well as the current latch. [Definitions][defs] · [Checked loop ranking][forest]

`pickSliceAcrossAndHoist?_placement` certifies both placements.
`pickSliceAcrossAndHoist?_routes` proves exact entry, feedback, and exit
transfers by following the retained bindings with corresponding typed
environments. The run, budget, and return theorems give equality at every
CF fuel, preserve the `k + 3` mapping, and preserve and reflect native
finite returns. [Theorem header][thms]

The fixture moves two definitions across two retained bindings. The second
retained binding reads the first, and the first reads the latch and saved
prerequisite. Their results advance the latch `3 → 9 → 15` over two
backedges while the saved results remain `3` and `2`. The fixture also
checks immediate exit and rejects an unused prerequisite, an absent
consumer, and a latch-dependent prerequisite. [Regression][regression]

## Proofs and scope

- `pickAndHoist?_placement` establishes that the pass used the legal
  preheader cut selected by the checked natural-loop ranking.
- `pickAndHoist?_routes` identifies the saved value as the original producer
  evaluated on captured inputs. It specifies the actual entry, feedback, and
  exit transfers and preserves the original latch and exit payload values.
- `pickAndHoist?_run_eq` proves equal CF observations at every fuel budget.
  `pickAndHoist?_budget` relates native budget `k` to CF fuel `k + 3` in the
  emitted loop. The preheader, final header test, and exit account for the
  three extra blocks. `pickAndHoist?_returns_iff` gives the finite return
  correspondence. [Theorem header][thms]

The profile uses the existing one-word latch and one-word return lowering.
The moved operation has the total, pure interpretation of the existing
scalar arithmetic and comparison dialect. The pass uses the source CFG's
supplied sound dominator certificate. The single-producer pass accepts
direct captures. The slice pass additionally accepts one selected earlier
invariant binding as a local dependency. It supports any gap between the
two selected bindings. Discovering larger dependency slices and moving
operations with effects or faults are outside these profiles. [Existing lowering][lower]

The regression uses a nonempty preheader and tests zero and two backedges.
Two feedback transfers keep the saved value at `2` as the latch advances
from `3` to `5` to `7`. A one-backedge budget at the same input returns
`none`. With a latch-dependent operand, the checker rejects the preheader
and ranks a header cut. The emitter rejects that move.
[Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Regression.lean
[lower]: ../../Silmaril/SSA/SeaOfNodes/Loop/MLIR/CF/Thms.lean
[forest]: sea-of-nodes-gcm-loop-forest.md
[diamond]: sea-of-nodes-gcm-hoist.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
