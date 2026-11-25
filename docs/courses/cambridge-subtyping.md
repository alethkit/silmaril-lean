# Structural subtyping

This slice follows chapter 6, *Subtyping and Objects*, pp. 83–88 of Peter
Sewell’s Cambridge Part IB *Semantics of Programming Languages* notes for
2025–26, dated 12 February 2026. The PDF matches the SHA-256 recorded under
`sewell2026semantics`. [Lecture notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.Subtyping
```

`Subtyping.L3Subty` instantiates the structural rules on L3 types. It gives
reflexivity, transitivity, record width, depth and
permutation, contravariant function domains, covariant function results and
products (slides 207–214), and componentwise sum subtyping (Exercise 34).
Width drops a suffix, as on slide 208. Use permutation followed by width to
drop fields in other positions. Record labels are distinct, as in the L3
grammar in §5.5.

`Subty.record_inv` recovers a source field of the same label and a subtype
of its target type for every field of the target record. The function,
product and sum inversion lemmas recover the component judgments through
reflexivity and transitivity. `Subty.reference_inv` proves that a subtype of
a mutable reference has exactly that reference type.

`Subtyping.HasType` uses the L3 syntax, contexts and store, with the
§5.5 typing rules plus subsumption. From `Γ ⊢ e : S` and `L3Subty S T`,
`Typing.sub` derives `Γ ⊢ e : T`. Each premise, including the annotated
binding and body premises of `let` and `let rec`, uses the extended
judgment (Exercise 35). `HasType.ofL3` and `StoreTyped.ofL3` embed core L3
derivations.

The checked type examples include nested width and depth, record
permutations and arrow variance. The projection application from slide 206
and a widened-sum match have L3 traces to `3`. A resettable counter used
through the `Counter` interface has a checked typing derivation. For
Exercise 33, two closed programs have type `int` under the respective
proposed rules for references, and each has a checked L3 run that gets
stuck at a missing-field projection.

Exercise 32 on pp. 87–88 has all four cases checked in the extended judgment.
The nested singleton has type `{p:{}}` by width within the outer field and
depth at the outer record. The `x.q.p` lambda returns an integer. The
lambda in part (3) has no type because its annotated function parameter
requires a field `p` and subsumption cannot add it to `{q = 3}`.
Part (4) uses permutation and width to type the argument with both fields.
[Exact derivations](../../Silmaril/Courses/Cambridge/Subtyping/L3Examples.lean)

### Object generators and method reuse

On p. 86, slide 219's `newCounter` allocates a reference to `0` and
returns a record of methods capturing it. The printed expression immediately
calls `inc`. Lean derives type `unit` and proves a trace to `skip` with
`1` in the new cell, for every choice of fresh address. [Slide 219][objects]

On p. 87, slides 220–221 give `counterClass`, the version of `newCounter`
that passes a freshly allocated `{p:int ref}` representation to the
class, and `resetCounterClass`. Lean checks each declaration and the
reductions of the constructors. The resettable object takes `get` and
`inc` from `super`. Its `reset` closes over the same representation.
Checked calls read, increment, and reset the supplied cell. [Slides 220–221][classes]

The examples use core L3 records, functions, references, and `let`.
The notes' `()` is represented by `skip`. The p. 87 declarations that use
`counterClass` are typed with that binding in scope. The reduction examples
close them with the printed `counterClass` definition and supply a call.
[Lean derivations and traces](../../Silmaril/Courses/Cambridge/Subtyping/ObjectExamples.lean)

The safety proofs use L3's value and reduction relations. With an empty
variable environment and a well-typed store, `Subtyping.progress` gives
either a value or an L3 step (Exercise 36). `Subtyping.preservation` retains
the expression's type and store typing across a step, allowing the
location environment to grow on allocation. `Subtyping.safety` applies
these results to every finite reachable configuration.

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=83
[objects]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=86
[classes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=87
[bib]: ../../references.bib
