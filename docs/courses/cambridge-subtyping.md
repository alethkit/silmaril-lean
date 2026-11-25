# Structural subtyping

This slice follows chapter 6, *Subtyping and Objects*, pp. 83–88 of Peter
Sewell’s Cambridge Part IB *Semantics of Programming Languages* notes for
2025–26, dated 12 February 2026. The PDF matches the SHA-256 recorded under
`sewell2026semantics`. [Lecture notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.Subtyping
```

`Subtyping.Subty` gives reflexivity, transitivity, record width, depth and
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

The checked examples cover nested record depth, distinct record orders that
subtype each other, the function type comparisons on slide 211, and the
`ResetCounter` to `Counter` comparison on slide 218. They also verify the
record-argument comparisons in Exercise 32(3–4) and rule out both proposed
directions of reference subtyping on slide 214 for the width example.

The rules work over a `TypeView` exposing the outer form of the caller’s own
types. The examples state these forms as hypotheses. Chapter 6 adds
subsumption to the L3 typing judgment from §5.5. From `Γ ⊢ e : S` and
`Subty view S T`, it derives `Γ ⊢ e : T`. It uses L3’s expressions,
stores and small-step rules. The L3 integration is pending for term typing
and reduction examples, the runtime counterexamples in Exercise 33,
`let` and `let rec` in Exercise 35, and progress and preservation with
subsumption (slide 215 and Exercise 36).

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=83
[bib]: ../../references.bib
