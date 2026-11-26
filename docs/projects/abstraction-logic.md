# Abstraction Logic

Import `Silmaril.Logic.Abstraction` for shaped syntax, evaluation and the institution.
`Silmaril.Logic.Abstraction.inst` is registered as `logic.abstraction.inst` in the logic graph.

| API | Contract |
| --- | --- |
| `Shape`, `Signature.Hom` | A shape has a valence (the number of shared binder slots) and a subset of those slots for each argument. Every slot occurs in some argument. Symbol maps preserve the whole shape, including overlaps. |
| `Term S k`, `Template S n` | A term has `k` local parameters. Each abstraction argument appends its own slots in increasing slot order (`Shape.slot`). A template is a term whose local context consists of its `n` parameters. A free name and its arity together identify a schematic operation. |
| `Term.rename`, `Term.instantiate`, `Term.subst`, `Rule.subst` | Rename or instantiate local parameters, or simultaneously replace free schemata by templates. The nameless local context makes the operations capture-avoiding. `Term.eval_instantiate`, `Term.eval_subst` and `Rule.holdsAt_subst` describe their denotations. |
| `Algebra`, `LogicalOrder`, `ValuationSpace` | Each abstraction acts on a tuple of operations on a single nonempty carrier. The logical order is a complete lattice of truth values with a retraction from the carrier. Admissible valuations are nonempty and closed under nullary updates and syntactically definable substitutions. `ValuationSpace.full` is the unrestricted case. |
| `Rule`, `Model.Sat` | A sentence has finitely many premise templates and a conclusion with no dangling local parameters. At each admissible valuation, the meet of truth values of all premises over all their parameter tuples lies below the truth value of the conclusion. The empty premise list tests truth at the top of the lattice. |
| `Rule.map`, `Model.reduct`, `Model.satisfaction` | Translating symbols in a rule and evaluating it in the target is equivalent to evaluating it in the reduct. The reduct keeps the carrier, truth structure and admissible valuations. It is closed under source substitutions because they translate to target substitutions and commute with evaluation. |

This development keeps the shared-slot declarations from the early papers and uses
the Primer's argument-template presentation locally. For instance, the scopes
`[{0}, {0}]` and `[{0}, {1}]` both pass two unary operations to the interpreter,
but declare different valences and scope sets. A named surface layer could retain
that distinction when resolving binders. Local indices already identify terms
modulo bound-name renaming in this representation. Premises use finite lists
as representatives. Reordering or duplicating premises does not change the
common-lower-bound condition. The institution uses discrete model arrows,
with hypotheses given by sets of rules via the library's existing institution
theory API. The scope here is fixed arities and semantic consequence. A named
parser, rule derivations, completeness and correspondence with a Practal kernel
are outside the current development.

## Rules for a deductive extension

Use Figure 4 of the pinned Primer for `Axiom`, `Assume`, `Add`, `Bind`,
`Subst`, `VarElim` and `Infer`. Use §3.5 and Appendix C to match the
semantic side conditions. Opening a premise for `Infer` should use fresh
nullary names for its local parameters. The opened names must be absent from
the free nullary occurrences of the supplying rule's premises. Use
`ValuationSpace.update_closed` when varying their values. For `Bind`, removal
requires that the removed parameters are unused in the premise body. For
`VarElim`, the eliminated nullary variable must be absent from the remaining
premises and conclusion, and its valuation can be updated to the carrier
representative of top using `LogicalOrder.classify_include`. Use
`Model.sat_subst` for the schematic substitution case.

The 2022 account hard-wires modus ponens and universal introduction into its
calculus and semantics. Obua's 2023 Practal note makes both theory rules
and expresses the premise of universal introduction as a template. The later
Primer uses general proof rules over rules and a logical order. With that
calculus, object-language introductions and eliminations belong in a theory.
Appendix L.2 gives universal introduction and instantiation, and derives
existential elimination with a template premise. Appendix L.1 gives the
implicative and equality presentations.

## First comparison to check

Use the existing unsorted first-order institution, `Silmaril.Logic.Institution.Examples.UFOL`.
Translate its operations and predicate symbols to valence-zero abstractions,
its variables to local parameters, and its universal quantifier to a unary
abstraction with one binder slot. In a canonical model built from a UFOL structure
with carrier `D`, use `D ⊕ Bool` with Boolean truth values and interpret the
universal abstraction by ranging over the embedded object carrier `D`. Keeping
truth values separate also supports singleton UFOL carriers. Check first that
translated formulas agree with `UFOL.Formula.Holds` at every object assignment
and that the canonical interpretations commute with signature reducts. A
comorphism should target a profiled institution with these interpretations and
a functor on model arrows. Arbitrary abstraction models give no fixed
interpretation to quantification, equality or connectives.

## Checks

```sh
lake build --wfail +Silmaril.Logic.Abstraction +Silmaril.LogicGraph.Nodes.Logic.Abstraction.Defs
lake env lean -DautoImplicit=false -DwarningAsError=true tests/logic/abstraction/Regression.lean
```

The regression checks overlapping binder scopes and a nonbinding argument under
an outer parameter, instantiation under a binder, a pointwise premise for
universal introduction, a countermodel for the premise-free assertion, and
satisfaction along a nonidentity signature map.

## Primary sources

The sources below are by Steven Obua. Artifact versions and SHA-256 hashes are
pinned in [references.bib](../../references.bib).

- `obua-2021-abstraction-logic`, *Abstraction Logic*, version 2.
  See “Algebra”, “Syntax”, and “Semantics”. [Author's report](https://obua.com/publications/abstraction-logic/2/)
- `obua-2022-abstraction-logic-foundation`, *Abstraction Logic: A New Foundation for (Computer) Mathematics*.
  See §§3–5 and §§10–14 for shaped syntax and the earlier model and proof rules. [arXiv:2207.05610v1](https://arxiv.org/abs/2207.05610v1)
- `obua-2023-axioms-are-inference-rules` and `obua-2023-logic-is-algebra`.
  The former documents the Practal change, and the latter gives shared-slot syntax
  and a distinguished-truth rule semantics in §§4–9. [Practal note](https://practal.com/press/aair/1) · [arXiv:2304.00358v1](https://arxiv.org/abs/2304.00358v1)
- `obua-2026-abstraction-logic-primer`, *Abstraction Logic: A Complete Logic over Second-Order Abstract Syntax*,
  full version dated November 16, 2026. Section 3, “A Primer in Abstraction Logic”, gives
  the syntax, ordered semantics, and rules used here. [Versioned Zenodo record](https://doi.org/10.5281/zenodo.24276226)
