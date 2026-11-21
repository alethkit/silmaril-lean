# Partial-equivalence constraints

The `Silmaril.Calculi.PERConstraints` calculus uses the existing `Formats.PER`
interface. A syntax is a carrier with total functions as morphisms. On a fixed
carrier, morphisms between PERs are relatedness-preserving endofunctions. The
total category allows the carrier to vary and forgets to the syntax category.
Morphisms act on all terms, including invalid ones, and are not identified just
because they agree on the PER quotient. The fixed-carrier category is not the
strict fiber of the forgetful functor: its arrows can have nonidentity syntax maps.

## Constraint semantics

| Form | Satisfaction by a PER |
| --- | --- |
| `EQ` on a set or finset | All pairs are related, including the diagonal. A nonempty collection is contained in the class of any chosen member. |
| `DISTINCT` on a set or finset | Every member is valid, and different members are unrelated. |
| `DISTINCTList` | Every occurrence is valid, and different positions are unrelated. Any duplicate makes the constraint unsatisfiable. Permutations preserve satisfaction. |

All three forms accept the empty collection and test validity on a singleton.
`Bound` is the sum of set EQ and list DISTINCT. A finite set DISTINCT can be
included by enumerating it **before** translation; `Bound.holds_ofFinsetDistinct`
justifies that inclusion. `distinct_list_iff_finset` shows what is lost by
forgetting occurrences: the list assertion also requires `Nodup`.

`All` and `Any` quantify over sets; `AllFinset` and `AnyFinset` restrict those
evaluators to finsets. CNF is an AND of ORs, and DNF an OR of ANDs. An empty AND
is true and an empty OR is false, at either level. `holds_ofFinsets` compares
the two-level finite evaluators with the set semantics. `CNF.toDNF` takes the
disjunction of all sets meeting every clause; it preserves satisfaction, SAT and
UNSAT, but is not a finite normalizer.

## Institutions and SAT

The CNF institution translates sentences forward and pulls PERs back along a
syntax function. Its model categories are discrete, **not** the categories of
PER-preserving syntax maps. The institution is a `Syntax ⥤ Room` with an `Inst`
registration in the logic graph (`calculi.per_constraints`). The same institution
restricts to shallow DASL link renamings and to extensional JSON atom replacement
at fixed object keys. JSON replacement uses the existing `Json.bind` laws; these
adapters do not impose a codec, wire profile or congruence on the PER models.

EQ translates by direct image. Occurrence DISTINCT translates by `List.map`,
which retains both positions even when their terms become equal. Set DISTINCT
transports by image only under an injectivity condition on the designated set.
The Boolean examples check both behaviors under a constant map: the imaged
set can become a valid singleton, but the translated list is unsatisfiable.
In particular SAT reflects from translation to source, but does not in general
preserve from source to translation.

A dictionary is a key-to-optional-bound function. Its conjunction compiles to
the CNF of its singleton clauses, preserving model satisfaction and therefore
SAT and UNSAT. SAT means a PER witness exists; UNSAT rules out every PER witness.
The logic graph registers and checks a satisfiable separation dictionary and an
unsatisfiable equality/distinctness conflict. There is no decision procedure or
claim of decidability for the infinitary language.

```sh
make check CHECK_TARGETS='Silmaril.Calculi.PERConstraints.Syntax.Formats.Thms Silmaril.LogicGraph.Nodes.Calculi.PERConstraints.Defs'
```
