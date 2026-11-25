# Semantic equivalence

This development follows chapter 8, pp. 98–102, of Peter Sewell’s Cambridge
Part IB *Semantics of Programming Languages* notes for 2025–26, dated
12 February 2026. The PDF matches the SHA-256 recorded for
`sewell2026semantics`. [Lecture notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.SemanticEquivalence
```

`L1.SemanticEquiv Γ T e₁ e₂` requires both phrases to have type `T` in
`Γ`. For every initial store covering `Γ`, they must both have infinite
L1 reduction traces or both return the same value in the same final store.
The initial store may contain other locations. The checked characterization
`L1.semanticEquiv_iff_may_return` compares returned observations of the
existing L1 operational model separately at each initial store. Determinacy,
terminal values, and safety justify the characterization, including the
case where both sets of returns are empty.

`L1.Context.preservesEquiv` proves Theorem 29 for the ten contexts on
slide 263. `L1.Context.plugAll_preservesEquiv` handles nested contexts.
The proof uses `L1.Evaluates`, a finite evaluation judgment proved
equivalent to reaching a value in the existing small-step semantics.
The while cases use induction on finite loop evaluations. The original
assignment proof also lifts infinite right-hand-side runs directly.

`L1.SemanticEquiv.seq_comm_of_disjoint` proves Exercise 42 over the union
of the typing environments. Its store argument tracks reads and writes in
each environment and retains the contents of every location outside both.
Conjecture 32 fails when the prefix sets a location from `0` to `1`
and the guard reads that location. The two orderings return different
integers and leave the same final store.

## L3 contextual equivalence

`L3.ContextualEquiv` implements Definition 33 using the core L3 typing
and small-step relations. General syntactic contexts include holes under
binders, inside record fields, and in either match branch. Plugging a
named phrase precedes scope resolution, so a context can bind names in
the phrase. The observation starts from the empty store once both
plugged phrases have closed unit typing. They must either both have
infinite runs or both have finite runs to `skip`, with independent
final stores. Reflexivity follows from L3 safety. Contextual closure
follows from composition of contexts.

Exercise 43 represents the assignable reference as the free name `l`.
The distinguishing context allocates a cell, binds `l`, and reads it
after executing the hole. The read selects termination for the assignment
of zero and an infinite loop for the assignment of one. The proof
rules out the opposite outcome for every allowed fresh address.

## Slide 256 stateful functions

The two closed `int → int` functions allocate a private cell initially
holding zero. One adds each input to its cell and returns the contents.
The other subtracts each input and returns the negated contents. The
slide uses subtraction. Core L3 has addition and comparison, so the
fixture implements negation as a recursive core function that moves its
integer argument toward zero. `negate_returns_iff` proves its exact
result for every integer while retaining the input store.
[Slide 256][notes]

`counter_returns_iff` characterizes all initialization returns from any
initial store. Every fresh address is permitted. `call_returns_iff`
proves the complete response and store for an integer call when the
cell holds the signed running total. In either representation the
response is the updated total, and the final store retains every other
binding. `counter_not_diverges` and `call_not_diverges` rule out an
infinite trace for initialization and for calls in this protocol.

`session_iff` characterizes every finite interaction formed by
initializing once and calling that closure with a list of integer
values. Both functions produce the same list of running sums. The
final private cells hold opposite totals at their chosen addresses.
`responses_agree` proves equality of the observable response lists
over the allocation choices. The proof observes exactly these finite
call sessions. Definition 33 would also require agreement in arbitrary
closing unit contexts, including contexts that store and pass the
function or interleave several instances.
[Checked fixture][stateful]

## Slides 257–258 pointer equality

Slide 257 compares two references of the same contents type by address.
Slide 258 allocates two private zero cells, `x` and `y`, in each function.
Both functions return `y` on a successful test and `x` otherwise. The
test compares the argument with `x` in `f` and with `y` in `g`.
[Slides 257–258][pointers]

The typed client binds the function once, calls it on a third fresh cell,
then calls it again on the first result. It compares the two results
by address. Both first calls return `x`. The second call returns `y`
for `f` and `x` for `g`. `probe_returns_iff` proves the resulting
`false` and `true` observations for every initial store and every
permitted fresh triple. Its converse realizes every such triple and
records the final store with the three zero cells inserted.

`observe_typed` checks a closing unit context around the probe.
`observe_returns_iff` gives its exact finite unit returns with `g` and
rules out any return with `f`. The false result selects the ordinary
L3 loop, and `f_selects_loop` proves the loop's infinite core trace in
the store left by each probe. The fixture gives a separation by this
specific context in a local call-by-value fragment with pointer equality.
It uses relational finite returns and delegates closed unit branches to
core L3. Core syntax, reduction and Definition 33 retain their existing
scope. The fixture establishes no correspondence for arbitrary contexts
in a full extension of L3. [Checked fixture][pointerfixture]

## Chapter coverage

| Notes | Checked in this slice | Remaining |
| --- | --- | --- |
| Slides 252–255, 259–262 and 265 | Typed L1 equivalence and its equivalence laws, arithmetic and store-sensitive examples, and the three store-reading contexts. The integer case uses a separate typed scratch location. | |
| Slide 256 | Exact initialization and integer-call sessions for both stateful functions, with every fresh choice and the signed final stores. | Contextual equivalence under Definition 33. |
| Slides 257–258 | Same-type address equality, checked examples and separation by a closing unit context for all fresh choices, in a local fragment. | |
| Slides 263–264, Theorem 29 and Exercise 41 | Congruence for all ten context forms and for nested contexts. | |
| Slides 266–267, Conjectures 30–32 | Sequencing associativity and distribution over the selected conditional branch (30–31). Counterexample to moving a prefix after the guard (32). Slide 255's fourth candidate preserves order and is proved. Determinacy makes the value-and-store observation single-valued. | |
| Slide 268 and Exercise 42 | Sequencing commutes for disjoint typing environments. | |
| §8.1, Definition 33 and Exercise 43 | L3 contextual equivalence using closing unit contexts, reflexivity, symmetry, closure under context composition, and the checked distinguishing context for the two assignments. | |

The restored-store example uses addition of `-1` for subtraction of one,
as L1’s operator grammar contains addition and comparison.

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=98
[bib]: ../../references.bib
[stateful]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/StatefulFunctions.lean
[pointers]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=99
[pointerfixture]: ../../Silmaril/Courses/Cambridge/SemanticEquivalence/PointerEquality.lean
