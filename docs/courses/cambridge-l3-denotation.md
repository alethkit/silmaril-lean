# Cambridge L3 data and reference denotation

The model interprets a fragment of the L3 language in §5.5 of Peter Sewell's
*Semantics of Programming Languages*, Cambridge Part IB 2025–26, dated
12 February 2026. The repository pins the source as `sewell2026semantics`.
[Course notes](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=78) ·
[Bibliography](../../references.bib)

Import `Silmaril.Courses.Cambridge.L3.Denotation`, also available through
`Silmaril.Courses.Cambridge.L3.Course`.

## Model and agreement

`Fragment` admits existing values, integer arithmetic and comparison,
conditionals, sequencing, while loops, pairs and both projections, both sum injections,
ordered records and label projection, allocation, dereference, and assignment.
It uses the original L3 expressions, types and stores. Function values can
be carried or stored as opaque values. Sum elimination, binding, function
application, and recursive functions are beyond this slice.

`denote` gives each expression a `StateT L3.Store SetM L3.Value` computation.
The clauses use the denotations of the operands. Record collection links the
return store of each field to the input store of the next field, in label
order. A value returns itself and the input store. Allocation returns every
address outside the current domain, each paired with its own extended store.
Reads use the current store. Assignment evaluates its right operand once the
left has returned an address, and writes only to an allocated cell. The
while clause uses the library's Elgot iteration for state over `SetM`.
A false guard returns unit. A true guard evaluates the body and continues
from the resulting store when the body returns unit. Each iteration can
carry a different allocation choice.

| Theorem | Contract |
| --- | --- |
| `adequate` | A value and final store belong to the denotation exactly when the original direct rules have a finite trace to that configuration. |
| `typed_return` | For a closed, typed source and matching store, every denotational return has the original type under a location typing that extends the original one. The final store has that typing. |
| `adequate_data` | The exact return theorem at typed data observations, with concrete final stores. |
| `data_return` | Every return of a typed data program can be observed at its declared data type. |

A `DataType T` witness interprets the original type `T` as Lean integers,
Booleans, unit, products, sums, or indexed record fields. Ground observations
use the first three cases. `DataType.value_typed` proves that representing an
observation as an L3 value preserves its type. `DataType.exists_result` proves
that each L3 value of that type represents some observation.

The soundness direction lifts subexpression traces through the corresponding
direct rule, including each record field in order. The finite-iteration
characterization yields the trace for a while return. Completeness reads a
source step backwards, transporting any return of its successor into the
denotation of its predecessor. The proof includes the fresh address named in
each allocation step. The model observes finite may returns with concrete
addresses and final stores. Must termination, divergence, location-renaming
quotients, and full abstraction require separate results.

The checked examples include a typed product containing a sum inside a
record, both effects of projecting an effectful record, a freshly
allocated cell read back as the same integer along two branches with
different final stores, and a typed loop that allocates and initializes
a cell before clearing its guard.
[Definitions](../../Silmaril/Courses/Cambridge/L3/Denotation/Defs.lean) ·
[Proofs](../../Silmaril/Courses/Cambridge/L3/Denotation.lean) ·
[Examples](../../Silmaril/Courses/Cambridge/L3/Denotation/Examples.lean)

## Higher-order store and games

L3 can save a function in a cell, replace it, and later call through that
cell. A compositional model for open terms must account for how a context can
call a returned function and how aliasing and private allocations affect
later calls. The function-cell example exercises the corresponding direct
rules. [L3 function cell](../../Silmaril/Courses/Cambridge/L3/Examples.lean)

Abramsky, Honda and McCusker give a fully abstract game model of an
ML-style language with general references. It relaxes behavioural
conditions of the pure functional game model and uses factorization to
reduce definability to the pure fragment. Laird's later trace semantics
for general references provides another reference point for specifying
interaction and hiding. These results apply to the languages and
observations defined in those papers.
[General-reference games](https://doi.org/10.1109/LICS.1998.705669) ·
[General-reference traces](https://doi.org/10.1007/978-3-540-73420-8_58)

Silmaril's Games region supplies legal plays, strategies, and composition
by interaction and hiding. An L3 application would need typed call and
return interfaces, a discipline for introducing and sharing locations, and
an account of which store interactions are hidden from the context.
Adequacy would then relate completed plays to L3 returns. A semantics
quotienting fresh names would also need a comparison theorem with the
concrete-address observations used here.
[Games library](../projects/games.md)
