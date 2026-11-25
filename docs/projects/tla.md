# Temporal Logic of Actions

Import [`Silmaril.Logic.Temporal.TLA.Thms`](../../Silmaril/Logic/Temporal/TLA/Thms.lean)
for the standalone semantics and proof rules. The core uses Lean's state types
and propositions and has no imports from other Silmaril developments.

The reference is Leslie Lamport's *The Temporal Logic of Actions*,
§§5.3–5.6 and Fig. 4 for Simple TLA, and §8.2 and Fig. 9 for flexible hiding.
*Specifying Systems*, §§8.1, 8.3, 8.8 and 16.2.4, provides the specification and
fairness conventions. [Paper](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf)
· [Book](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf)

## Typed Simple TLA

A behavior is a function `Nat → S` over a chosen state space `S`. A behavior
that settles in its last state still has infinitely many instants. A state
expression has type `S → V`, a state predicate has type `S → Prop`, and
an action has type `S → S → Prop`. These are denotations supplied by the
caller. `Action.current` reads the first state of the pair, and
`Action.prime` reads the second. `Action.enabled A s` quantifies over all
possible target states of type `S`. To restrict enabledness to legal targets,
encode that restriction in the action or in the state space.

The `Formula` constructors are a state predicate, `□[A]_f`, negation,
conjunction and `□F`. At instant `n`, `□[A]_f` tests every successive
pair starting at or after `n`, and `□F` evaluates `F` on every suffix
starting at or after `n`, including the current suffix. A bare action and
a temporal next operator are outside the grammar. `holds_suffix` relates
indexed evaluation to evaluation on the explicit suffix. `Sat` starts at
zero, and `Entails` is implication on every behavior.

The state observation `f` can be the identity, a projection, or a function
computing a tuple of relevant values. The modality stores an observation in
the state type's universe. The action-level operations also accept observations
from a different universe.

| Notation | Definition |
| --- | --- |
| `UNCHANGED f` | The observation has the same value in the source and target states. |
| `[A]_f` | `A ∨ UNCHANGED f`. |
| `⟨A⟩_f` | `A ∧ ¬UNCHANGED f`. |
| `◇F` | `¬□¬F`. |
| `◇⟨A⟩_f` | `¬□[¬A]_f`. |
| `F ~> G` | `□(F ⇒ ◇G)`. |
| `WF_f(A)` | Angle steps recur without bound, or disabled states recur without bound. |
| `SF_f(A)` | Angle steps recur without bound, or there is a suffix of only disabled states. |

Both fairness clauses use `ENABLED ⟨A⟩_f`. The theorems for WF and SF
characterize their premises as eventual continuous enablement and unbounded
recurring enablement, respectively. `strongFair_implies_weakFair` proves the
implication between them. `spec` assembles `Init ∧ □[Next]_f ∧ Live`,
where `Live` can be a conjunction of fairness clauses. `spec_invariant`
requires preservation on every bracket step, including steps that preserve
`f` while changing other state. `weakFair_progress` proves a leads-to
property from step preservation while waiting, enablement while waiting,
and an angle step that establishes the target.

## Stuttering and flexible hiding

A retiming begins at zero, holds or advances by one at each instant, and is
cofinal in `Nat`. It can expand each state into a nonempty finite run of
copies. It cannot postpone a later state forever. Two behaviors are
`StutterEquiv` when they admit retimings that produce the same behavior.
Lean proves this is an equivalence relation. For transitivity, the proof
synchronizes the two clocks on the middle behavior and proves both
synchronized clocks are cofinal.

This common-expansion presentation corresponds to the paper's equality of
stutter-reduced behaviors. Retiming preserves the ordered sequence of
maximal constant blocks and whether the last block is infinite. Conversely,
when those sequences agree, matching each pair of finite blocks at the
larger of their two lengths gives a common expansion. A final infinite
block can be matched one instant at a time. The Lean proofs use retiming
directly.

`Formula.holds_retime` proves invariance at corresponding instants under
repetition of **whole states**. Thus every Simple TLA formula, including WF
and SF, is invariant under `StutterEquiv`. The observation `f` in a
bracket only governs that bracket. Keeping `f` fixed can still change state
predicates, enablement, or another bracket. The theorem does not give
invariance under arbitrary changes to those other state components.

For split state `Visible × Hidden`, `hide p σ` holds when a full behavior
satisfying `p` has a visible projection stutter-equivalent to `σ`. The
hidden value can vary at each instant, and a hidden step can occupy time
inside a visible constant block. `hide_stutterInvariant` proves invariance
on visible behaviors for any predicate `p`. When `p` itself is
stutter-invariant on full behaviors, `hide_iff_lamport` proves agreement
with the paper's equation (49). At a full input `σ`, choose a full behavior
`ρ` in the stuttering class of `σ`, then existentially replace its hidden
component pointwise to obtain a behavior satisfying `p`.

## Checked examples and scope

[The example module](../../Silmaril/Logic/Temporal/TLA/Examples.lean)
proves progress for a weakly fair latch and rejects the run that leaves it off
forever. It separates WF from SF on an intermittently enabled action, proves
a parity invariant, and shows that hiding accommodates an internal
initialization step where pointwise existential projection fails.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Thms +Silmaril.Logic.Temporal.TLA.Examples
```

The current fragments are typed Simple TLA and semantic flexible hiding on
product states. General TLA syntax with flexible and rigid binders, the
full derivation calculus, machine closure, and the TLA+ operator
`-+->` (“while”) from *Specifying Systems* §16.2.4 remain separate work.
A next standalone milestone is scoped variable syntax for General TLA and
a satisfaction theorem for reindexing and refinement mappings. Those can
serve the later institution interface. The TLA+ AST, S-expressions, concrete
parser and Quint connection are later milestones.
