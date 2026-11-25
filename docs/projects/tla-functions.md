# Mathematical functions for the TLA+ tagged carrier

Import [`Data.Tagged.Functions.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Functions/Thms.lean)
for graphs and [`Data.Tagged.Collections.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Collections/Thms.lean)
for tuples, strings and records. These use the
[same tagged carrier as sets and scalars](tla-tagged-values.md).

| Reference | Checked interface |
| --- | --- |
| §16.1.7, pp. 301–304 | `Graph.ofFn s f` creates a mathematical graph with exact domain `s`. `Graph.lookup_ofFn` gives the result on its domain, and `Graph.lookup_eq_none` characterizes missing keys. `Graph.ext_of_domain_lookup` gives equality of graphs with the same domain and pointwise equal lookups there. The value constructor `Value.function` is injective. [Functions](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=319) |
| §16.1.7, p. 304 | `SetData.mem_functionSet` recognizes exactly graphs with the given domain and outputs in the range bound. [Function sets](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=322) |
| §16.1.7, p. 304 | `Graph.update` replaces one existing key. It preserves domain, changes the selected lookup, leaves other lookups alone, and is the identity outside the domain. [Single-key update](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=322) |
| §§16.1.8–16.1.10, pp. 305–308 | Tuples have integer keys from one through their length. Records take a list of field names and a value expression on those fields. Their keys are the same string values used for ordinary graph application. A string is the tuple of its characters, and the empty string is the empty tuple. All three constructors produce ordinary function values. [Records, tuples and strings](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=323) |

An internal graph is a Mathlib `ZFSet` of Kuratowski pairs of value codes.
Its well-formedness conditions require each element to be a pair and each input
to have at most one result. A function value pairs the function tag with that graph and is distinct
from any set or scalar value. Domain and range may be infinite.
`ofFn` forms a range indexed by the small subtype of members of its
domain. `functionSet` maps the Mathlib set of graphs over the exact domain
into function values. The graph and tuple equality laws use the same Lean
equality as the [tagged set laws](tla-tagged-values.md).

`Value.domain`, `Value.apply` and `Value.update` take the same
`Unspecified` function as the numeric operations. Missing application
keys and rejected function decodings route through that policy with their
operation and operands. A missing update key on a recognized graph is a
no-op. Updating a non-function uses the policy. Error form and policy
choices for a later source evaluator remain separate from these equations.
A caller can use `Graph.lookup` when it needs the distinction directly.

The character carrier is Lean `Char`. The string embedding is injective.
The record constructor represents a function on the set of the supplied
field keys and `lookup_record` gives the field result. Checking duplicate
field names in a source record literal, record-set syntax, multi-argument
source selection, and nested or multi-clause EXCEPT with `@` belong to
source lowering. The single-key update laws are the basis for rebuilding
the ancestors of an updated leaf. These APIs are mathematical and
noncomputable. They give neither source adequacy nor a finite evaluator.
