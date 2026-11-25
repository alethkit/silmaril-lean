# Mathematical sets and choice for TLA+

Import [`Silmaril.Logic.Temporal.TLA.Data.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Thms.lean)
for generic laws and [`Silmaril.Logic.Temporal.TLA.Data.ZFSet.Defs`](../../Silmaril/Logic/Temporal/TLA/Data/ZFSet/Defs.lean)
for the concrete `zfSetModel`. Both use the namespace
`Silmaril.Logic.Temporal.TLA.Data`.

A `Model V` fixes one Lean carrier `V`, its membership operation and its
choice policy. Both arguments of membership, the elements a set contains, the
witnesses of quantifiers and the result of choice all use `V`. Equality is Lean
equality. For any `s t : V`, `Model.ext_iff` characterizes their equality by
agreement on membership of every value.

## Operations and reference scope

Section and page numbers refer to Lamport’s *Specifying Systems*. The
links use the PDF page numbers.

| Reference | Model operation and law |
| --- | --- |
| §16.1.6, pp. 299–301 | `mem`, `ext_iff`, `empty`, `insert` and `enum` implement extensional membership and equality. Enumeration order and multiplicity disappear in the resulting set. [Set theory](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=317) |
| §16.1.6, pp. 300–301 | `sep s p` keeps exactly those members of `s` satisfying `p`. `image s f` contains exactly the values of `f` on members of `s`. `sUnion s` contains the members of members of `s`. The laws also cover binary union, intersection, difference and the powerset of a specified set through subset membership. [Set operations and formation](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=318) |
| §16.1.1, pp. 293–294 | `existsValue` and `forallValue` quantify over all of `V`. `existsIn s` conjoins membership and `forallIn s` uses membership as a premise. Over the empty set the existential is false and the universal is vacuous. These are the single-value binders, using `Prop` for a body’s truth. [Rigid quantification](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=311) |
| §16.1.2, pp. 294–296, equations (16.1)–(16.2) | `choose` has a witness iff its selected value satisfies its predicate, and equivalent predicates yield equal values. `chooseIn s p` uses the same policy on the conjunction of membership in `s` and `p`. Its result is in `s` and satisfies `p` whenever there is such a witness. [CHOOSE](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=312) |

Every unsatisfiable predicate yields the value of choosing on `False`, by
congruence. The generic API puts no further condition on that value. In
`zfSetModel fallback` it is the supplied `fallback`. Equal predicates at
different uses of the same model yield the same value. A failed bounded
choice has no guarantee of giving a member of its bound, even when the bound
itself is nonempty. Two instantiations can set different defaults.
[Choice witness and congruence](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=313)

Separation, image and powerset take a value serving as their set bound.
Unbounded quantification returns a proposition and unbounded choice returns
one value. Neither operation constructs a set of satisfying values.
`Model.not_universal` derives a contradiction from a set containing every
value by separating out the values that are not members of themselves.
`Model.exists_not_mem` gives a witness outside every set.
[The universal-set obstruction](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=83)

## Concrete realization and handoff

`zfSetModel` uses Mathlib’s `ZFSet.{u} : Type (u + 1)`, the quotient of
`PSet` by extensional equivalence. Membership is raw ZF membership on the
whole carrier, following the book’s pure-set account. Separation, union and
powerset use the existing Mathlib operations. For `image s f`, the subtype
of members of `s` has `Small.{u}` evidence, and its range under `f` is a
`ZFSet`. This works with arbitrary Lean predicates and functions on values,
bounded by a specified set. The concrete example over `ZFSet.omega` exercises
separation, image and choice with an infinite bound. The model is
noncomputable. [Pinned Mathlib ZFSet](https://github.com/leanprover/downstream-lean4/blob/569134c2fc750d92baa85d50cd925a7e20a93dd2/mathlib4/Mathlib/SetTheory/ZFC/Basic.lean)

Later interpretations can embed characters, integers and Boolean values into
this same carrier with injective encodings, and represent functions by tagged
graphs. Each encoded value will still carry raw ZF membership. Tags can
distinguish selected embeddings in a concrete realization. The generic set
laws give no cross-kind disjointness guarantee, because encoded values are
themselves sets in this model. Function recognition, exact-domain function
extensionality, common function identity for tuples, records and character
strings, and the corresponding numeric embeddings and `Nat`/`Int` membership
laws remain to be established. A future model’s domain and application
operations may have unspecified results away from their stated laws. Those
operations will need their own fixed, congruent interpretation, independently
of the fallback for unsatisfiable choice. All current set operations take
any carrier values as arguments. [Pure set theory and functions](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=317)
· [Unspecified values](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=85)

A future source interpretation can instantiate `Model` once for all
valuations and use the binders on interpreted predicates. Surface binders,
tuple patterns, Boolean values and coercion to predicate truth, source
adequacy and finite execution require separate layers. In particular,
`ZFSet.omega` here is a mathematical bound with no claim about standard
module resolution. [Boolean interpretations](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=314)

## Checks

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Data.Thms \
  +Silmaril.Logic.Temporal.TLA.Data.ZFSet.Defs \
  +Silmaril.Logic.Temporal.TLA.Data.Examples
scripts/check-layout.sh
```

The [examples](../../Silmaril/Logic/Temporal/TLA/Data/Examples.lean) use the
concrete model to check extensional enumeration, set identities, infinite
bounds, empty quantifiers, witnessed choice, and the common and independently
selectable defaults. The realization uses the standard Lean axioms allowed
by [repository policy](../../policy.toml).
