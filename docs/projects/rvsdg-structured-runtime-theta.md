# Whole-region θ with ordered runtime effects

The body of a checked [whole-region θ](rvsdg-theta.md) is a
[structured ordered region](rvsdg-structured-runtime.md). It returns a
two-way selector, the next carried values, and the current runtime in
that order. The selector is read after the body has finished. Stop
injects the values into the left summand of the Kleisli coproduct.
Continue injects them into the right summand. `close` applies the
computation category's Elgot iteration. [Definitions](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Theta/Defs.lean)

`close_of` identifies that categorical iteration with the underlying
lawful type monad's iteration. The ordered state specialization first
interprets the checked body in `StateM`, then embeds each total body call
in `StateT σ Part` and closes the loop. The existing StateT distributor
places the updated state alongside whichever result or feedback value is
selected. The first body execution is mandatory. The interpreter uses
effect sequencing and the coproduct with no interchange law between
effects.

`mem_denoteTotal` characterizes every finite returned tuple, including
its final runtime, by the numbered graph's `Returns` relation.
`denoteTotal_eq_none` characterizes undefinedness by an infinite sequence
of completed continuing body calls. The latter equivalence uses body
totality. In the generic categorical interpretation a body can itself
be partial, so the deterministic adequacy theorem has the stated total
body scope. A diverging loop produces no final state in the `Part`
observation. [Theorems](../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Theta/Thms.lean)

The [fixture](../../tests/ssa/RVSDGStructuredRuntimeTheta.lean) checks that
the decision to restart can depend on the updated runtime. It observes
the value and runtime after three executions, the mandatory execution
when entering at the stopping bound, and an always-continuing body.

The syntax covers one enclosing θ with a checked acyclic primitive/γ body.
Nested θ, multiple runtime wires, arbitrary firing schedules, general CFG
translation and sentence-level comparison are separate extensions.

## Reproduce

```sh
lake build --wfail +Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms
lake env leanchecker Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §5.1 Definition 5.5 on Elgot iteration.
  PDF SHA-256 `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
