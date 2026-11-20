# Relational determinism and checked fuel

`Silmaril.Semantics.Operational.Determinism` adds policies to `WithUB` without
changing `HasOpSem`, or making an executable selection the source of truth.

- `StepDetAt` is immediate successor uniqueness; `DetFrom` additionally requires
  immediate observation uniqueness at every reachable state. Neither says that
  any successor or observation exists. `ResultDetAt` compares complete finite
  outcomes. `NonTrapDetAt` means at most one non-trap payload, not “either every
  path traps or every path returns”; a trap can coexist with a unique payload.
  For Core, a non-trap payload also includes uncaught exceptions, not just
  successful returns. A different `ViewDetAt` can retain traps or compare only
  successful values. `Labelled.TraceDetAt` compares complete finite visible
  logs *and* outcomes, not all prefixes or infinite streams.
- `requireLocalDet` blocks primitive ambiguity at the offending state; it can
  reach UB after a nonempty prefix. `requirePrefix` tests every original prefix
  at the source and may instead report immediate UB. They give the same safety
  verdict for a common local test, not necessarily the same retained prefixes.
  `requireViewDet` rejects disagreement in the selected finite observation
  view. Those guards are policy, not properties of the Wasm standard. The policy
  relation only removes ordinary edges/observations and recovers all of them
  on its safe starts. The mixed `Permits` order admits more ordinary behavior
  and less immediate UB; unlike uniform relation inclusion, its join takes the
  union of ordinary behavior but the intersection of UB. Neither is the
  guarded `SafeRefines` preorder.
- `Oracle` is a sound certificate-backed choice, which may leave alternatives
  in the relation. `guard` needs a supplied `DecidablePred`; it does not infer
  an ambiguity decision from incomplete search. `run_sound` returns bounded
  relational evidence, even on exhaustion. Exhaustion means a known next step
  at the budget boundary, not UB or divergence. Unknown is not certified stuck.
  Completeness needs a finite witness, sufficient fuel, reachable determinism,
  terminal observations, safety, and an oracle that does not return unknown on
  the relevant reachable states.

## Actual Core boundary

`Silmaril.Wasm.Execution.Core.Entry.Determinism.Thms` proves finite result
uniqueness at the actual `SingleThreaded.Det.profile oracle` with `noHost`;
the existing normalization theorem gives a stronger final-state equality.
Raw trap propagation may take distinct primitive paths. On a `ConfigFree`
start, every host-free Core path transfers between **any two** `Numerics.Profile`
values, so its finite result is unique even at a spec profile. This hypothesis
excludes numeric-profile-sensitive operations and includes stored functions as
well as current code. It is not a claim that every `Profile.spec` is
deterministic. The regression exhibits two distinct admissible f32 NaN return
bit patterns at `Profile.spec nd` for either `nd`.

`normalOracle` uses the landed intrinsic numeric/local machine and
`State.raw_may_iff_bounded` connects finite observations in actual policy-gated
Core to a finite execution at some intrinsic fuel. The budgets are not raw
primitive-step counts. `driverOracle` takes an explicit soundness premise on
the actual Core driver; it reports unknown if neither the driver's step nor
its outcome classifier succeeds. It does not assert raw primitive uniqueness
or classify host callouts as UB.

The definitions are independent of the version tags and ISA feature tables.
Applying them to a SpecTec interpretation needs a verified relation/observation
transfer for that dialect; a tag alone supplies no such theorem. A host/game
adapter must specify the log alphabet, what inputs are fixed, and how callouts,
answers, host divergence, and pending requests are observed. No trace or
determinism claim about those open systems follows from `noHost`.
