# Straight-line Peggy field-heap reversion

`FieldHeap.Linearize.linearize` takes a typed, loop-free PEG with a final
state root followed by zero or more read-value roots. It recovers an
executable sequence of resolved field loads and stores for the
[field-heap profile](peggy-field-heap.md). The receiver and stored integer
operands are PEG parameters. The schedule consumes one state at each step
and passes its successor to the next step. A load register retains just
the optional integer. Output ports select registers in the original root
order, and repeated ports can select the same load.

The checker validates a decreasing demand phase over the whole node table.
Node numbers supply the default phase. Starting from the final state, it
follows store predecessors and the state projection of each load back to a
state parameter. It checks that every effect vertex belongs to the recovered
chain and that every value root projects a load on that chain. In particular,
it rejects a load observed through a value root when a store takes the
load's input token in place of its successor token. Even an effect with no
observed outputs must belong to the chain.

This is a partial solution to the problem described under “Reverting Uses of
the Heap” in §8.1. Figure 36 uses a shared heap snapshot in expressions that
need a valid execution order without snapshot copying. In this fragment a
load and store can name the same cell through different receiver parameters.
The load can then see different values before and after the store. Failures
can also impose an order because the first fault suppresses later accesses.
The checker takes the order from the explicit token edges. It rejects forks
even when a separate commutativity or ordering theorem could justify placing
both effects in a sequence. [§8.1, Figure 36 and discussion, pp. 60–61](https://arxiv.org/pdf/1012.1802v3#page=60)

## Checked contract

`demandWellFounded` supplies the guard for the original PEG's Figure 11
denotation. `effect_covered` shows that acceptance includes every field
effect. `run_eq_observe` proves equality between the executable schedule
and the ordered roots of the original graph for every typed input. Equality
includes the full final heap, its first fault, and all selected read
values. A completed faulting read has root value `some none` in the
Figure 11 observation.

The fixture recovers load–store–load, observes the loads in reverse order
with a repeated port, and checks aliased receivers, sticky faults, and
retention of a read made before a fault. The forked graph differs only in
one token edge and is rejected even though it passes the acyclic demand
check. [Definitions](../../Silmaril/SSA/Peggy/FieldHeap/Linearize/Defs.lean) · [Theorems](../../Silmaril/SSA/Peggy/FieldHeap/Linearize/Thms.lean) · [Fixture](../../tests/ssa/PeggyFieldHeapLinearize.lean)

The supported operations are field loads and stores and their projections.
This fragment has no reversion for reachable control nodes, the synthetic
`forwardRead` opcode, arrays, calls, or exception handlers. No alias
analysis, effect reordering, or general §7 CFG construction is required.

```sh
lake build --wfail +Silmaril.SSA.Peggy.FieldHeap.Linearize.Thms PeggyFieldHeapLinearizeTests PeggyFieldHeapTests PEGCoreTests
lake env leanchecker Silmaril.SSA.Peggy.FieldHeap.Linearize.Thms
lake env leanchecker tests.ssa.PeggyFieldHeapLinearize
```
