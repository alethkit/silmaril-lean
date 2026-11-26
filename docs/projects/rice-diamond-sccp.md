# Conditional constant propagation on a typed diamond

The analysis instantiates the [optimistic finite-height solver](rice-optimistic-finite-height.md)
for the native pure `Diamond.Graph`. It uses the dual of the
dissertation’s descending order. The solver starts at bottom, adds executable
Region occurrences, and raises facts along the order from bottom through exact
constants to overdefined. This covers the simultaneous equations and the interaction between
unreachable paths and constant propagation in Rice §§3.2–3.7 for one diamond.
[Source mapping](sea-of-nodes.md#rice-dissertation) ·
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Native graph](../../Silmaril/SSA/SeaOfNodes/Diamond/Defs.lean)

Each Region slot records its incoming projection, independently of the order
of the projections at the If. The assignment contains the set of marked Region
slots, a flat fact for each typed producer port, and a flat fact for the
returned Φ. The unconditional pure producers form an acyclic table. The
transfer computes their facts in dependency order using the model’s existing
primitive operations whenever their operands are constant. Each branch and Φ
equation reads the previous assignment. A constant predicate marks its
matching slot, an overdefined predicate marks both, and bottom marks neither.
Φ joins only operands at marked slots. A caller with an unclassified runtime
input supplies `.overdefined`. Bottom covers no concrete value.
[Equations](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Defs.lean) ·
[Flat domain](../../Silmaril/Semantics/Dataflow/Flat/Defs.lean)

`transfer_mono` proves monotonicity in the assignment order. `phiFact_le_iff`
characterizes the Φ fact as the least upper bound of exactly the marked
operands. `solve` uses a rank budget of two for the Region, two per producer
port, and two for Φ. `solve_fixed` and `solve_isLeast` give the result of
bounded iteration. For every concrete entry covered by the supplied entry
facts, `solve_sound` marks its selected occurrence and covers its native
denotation. `solve_read_covers` covers every argument or producer wire, and
`solve_returns` states coverage for the native finite return relation. At an
inferred constant, coverage means equality.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Thms.lean)

The example has its false projection first in Region order. Its true operand
adds a shared literal producer to itself to get 14, and its false operand is
99. Each result reports the first and second Region flags followed by the
Φ fact. With a known true guard, only the second operand participates. With an
unclassified guard, both operands participate and the result is overdefined.

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example.Defs

open Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Example

#eval report .onFalse (.constant ⟨true⟩)   -- (false, true, Silmaril.Semantics.Dataflow.Flat.constant 14)
#eval report .onFalse (.constant ⟨false⟩)  -- (true, false, Silmaril.Semantics.Dataflow.Flat.constant 99)
#eval report .onFalse .overdefined         -- (true, true, Silmaril.Semantics.Dataflow.Flat.overdefined)
```

The regression also checks the opposite Region order, the dormant bottom
case, and the concrete source denotations on both branches.
[Example graph](../../Silmaril/SSA/SeaOfNodes/Diamond/SCCP/Example/Defs.lean) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/SCCP/Regression.lean)

The profile has one If, one Region, one returned Φ and total, unpinned
primitives. Loops, general CFG dataflow, effects, optimized sparse
scheduling, and graph rewrites are separate developments.

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Diamond.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.SCCP.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
