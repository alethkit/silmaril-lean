# PEG single-loop carried values and structured RVSDG θ

The bridge covers a canonical typed PEG with one loop, two ordered carried
slots and a total pure dialect model. The slots can have different sorts.
The two parameters initialize separate PEG θ nodes. Three typed operations
read the same current tuple and compute the exit test and the two next
components. One pass finds the first true test. The roots are ordered eval
nodes that sample the two θ streams at that pass.

| PEG vertices | Role |
| --- | --- |
| 0, 1 | Initial values from the two parameter slots |
| 2, 3 | The left and right θ streams |
| 4, 5 | Exit predicate and its shared pass |
| 6, 7 | The two feedback updates, each using the old tuple |
| 8, 9 | The ordered eval roots, both sampling at vertex 5 |

`Form` is a syntactic witness that an actual `PEG.Graph` is this typed
table for three specified instructions. `compile` constructs the numbered
RVSDG θ from that witness. Recognition of other table numberings and
recognition of general PEG loop bodies are separate extensions.
[Definitions](../../Silmaril/SSA/PEG/Bridge/Theta/Defs.lean)

## Sequencing and polarity

The generated whole-region `RVSDG.Theta.Graph` has the two carried value
ports on entry and exit. Its body first tests the current tuple. A true PEG
test produces RVSDG tag zero. The corresponding γ child forwards the
unchanged tuple. A false PEG test produces tag one. That γ child executes
the two update vertices in order, with both vertices reading the original
child arguments. The body returns the same tag followed by the γ outputs.
RVSDG exits on zero and feeds back the next tuple on one.
[Existing RVSDG θ interface](rvsdg-theta.md)

For first exit `k`, the RVSDG θ has `k` continuing activations followed by
the mandatory stopping activation. Its output is the input to that final
activation, which is also the PEG state at index `k`. An initially true test
executes the body once and returns the initial tuple. `Loop.body_run`
evaluates the actual numbered body. `Loop.returns_iff_firstExit` proves
both directions using the existing `Theta.Iterate` rules.
[Theorems](../../Silmaril/SSA/PEG/Bridge/Theta/Thms.lean)

## Guarded Figure 11 observation

`Loop.rank_check` verifies a finite lexicographic rank for every dependency.
The outer phase handles arbitrary sampling indices, the counter handles
feedback, and the final phase handles the remaining same-index edges.
The source proof uses the equations solved by the guarded `Graph.denote`.

Induction from the defined input tuple proves that both θ streams are
defined and equal to the carried state at every index. The three primitive
equations strictly collect both operands before applying their total
interpretations. The resulting predicate has a defined prefix, so
`Loop.pass_eq_some_iff` identifies its first true sample. Each eval
independently uses the Figure 11 monotonization condition for every
earlier sample of its carried stream. This gives the ordered observation
at the same count from every ambient index.
[Guarded PEG semantics](../../Silmaril/SSA/PEG/Semantics/Thms.lean) ·
[Source proof](../../Silmaril/Proofs/SSA/PEG/Bridge/Theta/PEG.lean)

`returns_iff_observe` equates a finite RVSDG return with the PEG's fully
defined ordered roots. `denotePart_eq_some_iff_observe` composes with the
existing partial-value adequacy theorem for the graph's packed result.
These theorems cover finite returns with total primitives. The fixture
also checks absence of a finite return for a constantly false predicate.
Bottom-producing or effectful primitives, general loop extraction, and
a cross-semantics divergence theorem remain separate obligations.
[Existing partial-value adequacy](rvsdg-theta-categorical.md)

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Bridge.Theta.Thms PEGStructuredThetaTests PEGCoreTests PEGIRBridgeTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
for module in \\
  Silmaril.SSA.PEG.Bridge.Theta.Defs Silmaril.SSA.PEG.Bridge.Theta.Thms \\
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.PEG Silmaril.Proofs.SSA.PEG.Bridge.Theta.RVSDG \\
  tests.ssa.PEGStructuredTheta; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \\
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The regression reduces the compiled numbered body at counter/accumulator
states `(0, 5)`, `(1, 6)` and `(2, 8)`, checks the first pass count and both
eval roots at that exit, and checks immediate exit from `(2, 99)`.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
