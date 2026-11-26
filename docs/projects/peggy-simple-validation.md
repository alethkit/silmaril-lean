# Checked Peggy optimization of SIMPLE

`SimpleValidation.optimize eqPrim rules depth source` takes an existing typed,
loop-free SIMPLE program with a single return. It builds and checks the
frontend's PEG rank, runs the contextual optimizer's bounded discovery and
receipt replay, and synthesizes and checks a reversion schedule for the chosen
graph. The result is an `Except`. An accepted result carries the replayed
candidate and typed schedule. Its `output` is an existing SIMPLE program,
executable with `Program.runLoopFree`. The caller supplies an instruction
signature, decidable primitive equality, rule schemas and a search depth.
The pipeline derives the graph, receipts and schedule.
[Pipeline API](../../Silmaril/SSA/Peggy/SimpleValidation/Defs.lean)

The contextual selector minimizes its existing count of distinct reachable
primitive and φ vertices among the explored candidates. Depth zero selects
the unchanged graph. If automatic reversion rejects the selected candidate,
the pipeline returns `Rejection.reversion`. A checked rewrite can still
lead to placement that would require duplicate writers. The pipeline tries
one selected graph per call. The rank check also has an explicit rejection
case, and `frontendRank_valid` proves it accepts every graph emitted by the
frontend.
[Contextual discovery and replay](peggy-contextual-optimizer.md) ·
[Automatic reversion](peggy.md#automatic-scheduling)

## Successful returns

For any interpretation satisfying the supplied rule laws, if the source
has a finite successful execution returning `v`, `Accepted.returns`
gives a successful execution of the emitted program on the same input with
return `v`. `optimize_preserves_returns` states this postcondition directly
for an `ok` result, and `Accepted.runLoopFree` gives the executable result
`some v`. The composition follows the three semantic boundaries.

1. The successful source execution gives a defined Fig. 11 root.
2. Replay soundness equates the original and optimized Fig. 11 observations,
   including bottom. Rule laws quantify over partial substitutions, and
   the proof transports the source's defined root through this equality.
3. The checked reverter turns the optimized defined root into a successful
   SIMPLE return. It keeps the unselected arm unevaluated.

The theorem covers defined returns with pure, possibly partial primitives.
Failure and divergence correspondence remain outside the contract. The
pipeline does not evaluate a source during optimization.
[Public theorems](../../Silmaril/SSA/Peggy/SimpleValidation/Thms.lean)

## Worked example

The fixture starts with an input flag and natural number `x`. The true
arm binds `(x + x) + x` once and adds that binding to itself. The false
arm runs a primitive whose result is undefined. The rule replaces
`(x + x) + x` by a unary `triple x`, with its law checked for both defined
and undefined substitutions. Discovery finds the site below the shared
sum and the enclosing φ. The fixture supplies no match, receipt or
schedule.

| Search depth | Reachable applications before → after | Primitive assignments in emitted SIMPLE | Input `(true, 14)` |
| --- | --- | --- | --- |
| 0 | 5 → 5 | `add, add, add, bad` | `some 84` |
| 1 | 5 → 4 | `triple, add, bad` | `some 84` |

The false-arm assignment stays guarded. The fixture also checks the
explicit reversion rejection for a program with one value whose writer
the scheduler would duplicate across both arms.
[Executable fixture](../../tests/ssa/PeggySimpleValidation.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.Peggy.SimpleValidation.Thms PEGCoreTests PeggyEggTests PeggySimpleValidationTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PeggySimpleValidation.lean
```
