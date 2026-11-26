# Finite-height optimistic iteration

Click’s Rice dissertation defines the optimistic assumption as starting
at the top and proceeding down to the greatest fixed point (§2.1,
printed pp. 9–10). §§3.2–3.4 cast simultaneous equations as a monotone
operator on a finite-height lattice of assignments. The proof in §3.4
starts at the meet identity `⊤`. This development uses the order dual.
In Lean, `x ≤ y` means `y ≤ x` in the dissertation’s order, the
optimistic initial element is `⊥`, and a least fixed point here is the
greatest fixed point there. Initialization expresses the analysis’s
provisional optimistic assumption.
[Source mapping](sea-of-nodes.md#rice-dissertation) ·
[Rice record](https://hdl.handle.net/1911/16807)

`HeightBound` gives a natural-number rank, a uniform upper bound `b`,
and a proof that rank increases along every strict ascent. It counts
strict steps. A chain of `d` elements has `d - 1` strict steps.
`HeightBound.solve` applies a monotone `OrderHom` to bottom exactly
`b` times using Mathlib’s executable `Function.iterate`. The core solver works
over partial orders with bottom. The chain is
ascending, and an equality between consecutive iterates persists. A
further strict step at index `b` would therefore force `b + 1`
strict rank increases from a nonnegative initial rank.
[Solver definitions](../../Silmaril/Semantics/Dataflow/FiniteHeight/Defs.lean)

`solve_fixed` says that the computed assignment satisfies the equations.
`solve_isLeast` proves leastness, and `solve_le_of_prefixed` bounds the
solution by every assignment `x` with `f x ≤ x`. On a complete lattice
`solve_eq_lfp` identifies the answer with Mathlib’s `OrderHom.lfp`.
`solve_dual_isGreatest` states the result in the dissertation’s order.
For domains with decidable equality, the existing `iterateUntilStable`
returns the same answer with `b + 1` units of fuel, including the
stability check after the last possible strict step.
[Public theorems](../../Silmaril/Semantics/Dataflow/FiniteHeight/Thms.lean) ·
[Existing iteration](../../Silmaril/Semantics/Dataflow/Iteration.lean)

The two-variable example has `x' = max 1 y` and `y' = x` over
`Fin 3 × Fin 3`. Each round reads both old coordinates. The run goes from
`(0, 0)` to `(1, 0)` to `(1, 1)`. There is also a fixed point
`(2, 2)`, and the leastness theorem selects `(1, 1)`. The product
certificate gives a four-step bound.

```lean
module

import Silmaril.Semantics.Dataflow.FiniteHeight.Cycle.Defs
meta import Silmaril.Semantics.Dataflow.FiniteHeight.Cycle.Defs

open Silmaril.Semantics.Dataflow
open Silmaril.Semantics.Dataflow.FiniteHeight

#eval Cycle.answer                       -- (1, 1)
#eval iterateUntilStable Cycle.step 2 ⊥  -- none
#eval iterateUntilStable Cycle.step 3 ⊥  -- some (1, 1)

example : IsLeast {x | Cycle.step x = x} Cycle.answer :=
  Cycle.height.solve_isLeast Cycle.step
```

`HeightBound.finset` uses cardinality for finite sets ordered by
inclusion. `HeightBound.pi` sums per-variable bounds, and
`HeightBound.prod` combines the edge and value budgets. These certificates
apply to finite-height value domains with infinitely many incomparable
constants. Using them for SCCP requires a monotone edge/value transfer,
a concretization, and a soundness argument for the resulting facts.
The solver covers §3.4’s simultaneous iteration. The sparse scheduling,
invalidation, and cost analysis of §3.5 are separate obligations.

The pinned Rice scan has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice scan](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content)

```sh
make check CHECK_TARGETS='+Silmaril.Semantics.Dataflow.FiniteHeight.Cycle.Defs +Silmaril.Proofs.Semantics.Dataflow.FiniteHeight.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.Semantics.Dataflow.FiniteHeight.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
