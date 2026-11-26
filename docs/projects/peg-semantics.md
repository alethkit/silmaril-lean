# Guarded PEG denotation

The PEG denotation implements Equation (5.1) and Figure 11 of Tate,
Stepp, Tatlock and Lerner’s *Equality Saturation: A New Approach to
Optimization*. The source is arXiv:1012.1802v3, PDF SHA-256
`5bb3630c9a2a4766c5614b19148e865ee0797c693607b2cdd700b27c38df0b94`.
The [PEG core roadmap](peggy.md) gives the surrounding milestones and the
counterexample to the printed Definition 5.1 guard. [Figure 11](https://arxiv.org/pdf/1012.1802v3#page=23)

## Figure 11 and observations

An `Interpretation` gives each data sort a carrier and interprets each
typed instruction as a pure partial function. Boolean and count sorts
use Bool and Nat. Primitives are lifted strictly and pointwise. Parameter
slots receive defined input values. The valuation assigns an
`Option` value to every node and every `Fin loops → Nat` index. A
node’s value or undefinedness always refers to that whole index vector.

- φ reads the guard and then the selected arm. A bottom guard produces
  bottom even when both arms would return the same defined value.
- θ reads its initial operand when its loop count is zero. At
  `k + 1` it reads the feedback operand with just that loop's count
  set to `k`.
- Eval reads its requested count at the original index. For a defined
  count `k`, it reads the sampled operand at `k` only if every
  earlier sample is defined, holding all other coordinates fixed.
- Pass returns the least true among the monotonized predicate samples
  in its loop coordinate. A true after a bottom prefix cannot satisfy
  this search. Pass returns bottom if there is no eligible true.

Bottom is the single `⊥` of the paper. It records no distinction among
primitive failure, divergence, and absence of a defined pass result.
This interface gives no separate trap or divergence observation. In
particular, an unending all-false predicate and one that reaches bottom
without a true both produce bottom at pass. `Graph.observe` reads the
ordered tuple of roots at a supplied index and retains the `Option`
for each slot. It performs no projection or whole-tuple definedness
check. The unbounded pass and simultaneous denotation are
noncomputable specifications. The rank checker is executable and
introduces no fuel bound on denotation.
[Definitions](../../Silmaril/SSA/PEG/Semantics/Defs.lean)

## Repaired Theorem 1

`Graph.Demand child parent` follows a typed operand edge from parent
to child and records its possible change of index. A sample edge can
set its loop coordinate to **any** Nat. This single relation covers
eval’s selected index, all of its prefix queries, and pass’s unbounded
search. The dependency relation conservatively includes both φ arms.
The interpretation still reads only the selected arm.

`Graph.demandWellFounded` proves that the stronger
`Graph.WellFormed` guard from the core implies well-founded demands.
The proof uses the finite loop forest, the feedback-cycle condition,
and the enclosing **feedback edge** condition. The separate scope
condition in `Graph.WellFormed` is unnecessary for termination of
demands. Every sufficiently late vertex/role pair of a hypothetical
infinite demand chain recurs. Repeated pairs give closed walks whose
edge roles all recur. The enclosing feedback condition lets induction
on loop ancestry rule out a recurrent sample before ruling out
recurrent feedback in each coordinate. In a coordinate without late
resets, the counts are nonincreasing and cannot strictly decrease
arbitrarily late. The first cycle condition forces a recurrent feedback
edge, giving the contradiction.

`Graph.existsUnique_solves_of_wellFormed` is the repaired Theorem 1.
It gives a unique simultaneous solution for every interpretation and
input assignment. `Graph.denote_solves` proves that the
well-founded definition satisfies Equation (5.1), and
`Graph.solves_unique` is its extensional uniqueness principle.
The more general `Graph.existsUnique_solves` accepts any proof of
well-founded demands.

An independent route uses `DemandRank.check`. A certificate is a
finite lexicographic list of vertex phases and loop counters. Each
operand occurrence checks for a strictly decreasing component after
only unchanged components. At a sampling edge, the sampled counter
is unknown and can only occur after a component has already
decreased. `Graph.demandWellFounded_of_check` proves soundness over
all indices. Certificate synthesis and completeness of the rank class
remain open.
[Demand and certificates](../../Silmaril/SSA/PEG/Semantics/Demand.lean) ·
[Theorem headers](../../Silmaril/SSA/PEG/Semantics/Thms.lean)

## Interface for Peggy dialects

An opcode map leaves the demand relation unchanged. For a target
interpretation `M`, `Interpretation.reduct f M` retains the carriers
and precomposes the primitive interpretation with `f`. The graph-level
`equation_mapOps` transports the equation for arbitrary candidate
valuations. `denote_mapOps` and `observe_denote_mapOps` give exact
equality of the solution at every request and equality of the ordered
root tuple, including bottom in any slot. The hypotheses are
`WellFounded` for the source and mapped demand relations, and
`demandWellFounded_mapOps` transports the certificate-free
well-foundedness proof. These are the denotation laws for a follow-up
satisfaction condition.

## Replay

```sh
lake build --wfail +Silmaril.SSA.PEG.Semantics.Thms PEGCoreTests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEG.lean
lake env leanchecker Silmaril.SSA.PEG.Semantics.Thms
lake env leanchecker tests.ssa.PEG
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Semantics.Thms PEGCoreTests'
```

The fixtures check a conditional with a bottom guard or arm, a nested
cyclic graph under both admission routes, the actual demand cycle in
the printed-guard counterexample, arbitrary sampled counts, and a
counting loop that returns at two. They also check eval with an
undefined earlier sample or count, pass blocked by an earlier
undefined predicate, a never-true predicate, and exact opcode
transport. [Lean fixture](../../tests/ssa/PEG.lean)
