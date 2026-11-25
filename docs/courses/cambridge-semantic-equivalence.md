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

`L1.Context` presents the ten contexts on slide 263. The assignment case
`L1.Context.assign_preservesEquiv` lifts both finite and infinite
right-hand-side runs using the existing assignment rules. The finite case
uses type preservation to obtain the common integer and store for the final
write.

## Chapter coverage

| Notes | Checked in this slice | Remaining |
| --- | --- | --- |
| Slides 252–255, 259–262 and 265 | Typed L1 equivalence and its equivalence laws. `2 + 2` and `4` agree. Two programs returning `4` leave different stores and the add-and-read context returns `4` and `5`. Increment followed by decrement is equivalent to writing the original contents. A checked looping example separates divergence from return. | General store-distinguishing contexts for each result type on slide 262. |
| Slides 256–258 | | Stateful-function examples and the example with the temporary pointer-equality extension. |
| Slides 263–264, Theorem 29 and Exercise 41 | All ten context forms, plugging, and the worked assignment case. | Congruence for the other nine forms and composition of nested contexts. |
| Slides 266–267, Conjectures 30–32 | Determinacy of returned configurations and the characterization by return sets. | Sequencing associativity and the proposed conditional laws. |
| Slide 268 and Exercise 42 | | Commutation of sequences with disjoint location environments. |
| §8.1, Definition 33 and Exercise 43 | | L3 contextual equivalence using closed unit contexts and termination observations. Construct the distinguishing context for the two assignments. |

The restored-store example uses addition of `-1` for subtraction of one,
as L1’s operator grammar contains addition and comparison.

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=98
[bib]: ../../references.bib
