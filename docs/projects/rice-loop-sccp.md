# Conditional constant propagation on a single pure loop

`Loop.SCCP` analyzes the existing native `Loop.Graph` with a typed carried
bank, a preheader table and a header table of total pure primitives. The
native step evaluates the header table on the old latch, then reads the guard.
A tail-tested body is represented by wiring that guard to a body result.
The fixture tests the updated word and sends that same word to feedback or
return. There is one entry occurrence, one feedback occurrence, and one exit.
[Native loop](../../Silmaril/SSA/SeaOfNodes/Loop/Defs.lean) ·
[Tail-tested quad lowering into the same graph](sea-of-nodes-quad-loop.md)

The simultaneous assignment consists of a set of marked occurrences, one
flat fact per carried port, and one flat exit fact. The preheader computes
the entry column. A transfer evaluates the shared abstract producer table on
the old bank, obtaining the guard, the whole feedback column, and the exit value. The
guard marks the possible successors of an enabled header. Φ joins the entry
and feedback operands pointwise. Every port uses the same occurrence marks,
and the entire feedback column reads the old bank before any join. The exit
value likewise contributes when the exit is marked. A changed latch can
therefore change the guard and feedback in a later round.
[Equations](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Defs.lean) ·
[Shared producer laws](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Dataflow/Thms.lean)

`transfer_mono` and `phiFacts_le_iff` prove monotonicity and the
occurrence-indexed join rule. `BankDecidableEq` supplies equality at each
carried port. The analysis starts from optimistic bottom, the dual of the
dissertation’s optimistic top. For `n` carried ports the rank budget is
`3 + 2n + 2`, using three marks and two possible increases for each of the
carried and exit facts. `solve_fixed` and `solve_isLeast` certify the
computed cyclic least fixed point. `solve_arrives` marks every finite
native prefix and gives `BankCovers` for the whole latched tuple, including
prefixes with no eventual return. `solve_step`,
`solve_returnsAfter`, and `solve_returns` cover the actual successors and
finite returns. Concrete execution fuel is independent of the analysis
budget. Marks overapproximate the concrete edges, and a covered constant
gives equality on each corresponding concrete observation.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Thms.lean)

The eight-bit example starts at zero. With increment one and the external
flag true, the latch is initially constant zero. The enabled feedback
supplies one, making the latch overdefined. The native loop exits with
three after two backedges. With increment zero and an unclassified flag,
both successors are marked, and the latch and exit both retain constant
zero. When the flag is known false, the unequal feedback operand stays
excluded, and the first activation returns one.

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example

#eval changingLatch 3                    -- constant 0 before feedback contributes
#eval changingLatch 4                    -- overdefined
#eval run 1 true 2                        -- some 3
#eval report 0 .overdefined              -- (true, true, true, constant 0, constant 0)
#eval report 1 (.constant ⟨false⟩)       -- (true, false, true, constant 0, constant 1)
```

The two-field fixture carries a Boolean and an eight-bit word. At the
fixed point the Boolean stays true and the word becomes overdefined.
The native run exits with three after two backedges. A second fixture
computes the next Boolean from the old word and uses the old Boolean to
decide whether to increment the word. Its first feedback takes
`(false, 0)` to `(true, 0)`. The same backedge alone produces those two
constants in the abstract Φ equation. Reading the updated Boolean while
computing the word would give one.

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.Example.Bank

#eval invariantReport         -- (true, true, (constant true, overdefined), overdefined)
#eval runInvariant 2           -- some 3
#eval nativeCrossFeedback      -- some (true, 0)
#eval abstractCrossFeedback    -- (constant true, constant 0)
```

The source is Cliff Click’s Rice dissertation, *Combining Analyses,
Combining Optimizations*. Chapter 3 §3.2 Figure 3.1 (printed p. 17) gives
a tail-tested SSA loop with entry and feedback operands. §3.3 Figure 3.3
(p. 22) gives the constant domain, and §3.4 (pp. 24–25) proves optimistic
fixed-point iteration. §3.6 Figure 3.7 (p. 26) gives cyclic reachability.
§3.7 Figure 3.8 (p. 28) combines reachability gates and conditional
constant tests, and §3.7.2 Figures 3.9–3.10 (pp. 29–30) apply the mixed
equations to the example. The pinned scan has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice record](https://hdl.handle.net/1911/16807) ·
[Pinned scan](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content) ·
[Source mapping](sea-of-nodes.md#rice-dissertation)

The analysis covers one Loop Region and uses the shared strict flat
lifting of primitives. Operator-specific precision such as Figure 3.4’s
multiplication rule, interior control, sparse scheduling, GVN, rewrites,
and effects remain separate.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.SCCP.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
