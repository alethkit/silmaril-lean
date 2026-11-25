# Tagged set and scalar values for TLA+

Import [`Data.Tagged.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Thms.lean)
for set laws and
[`Data.Tagged.Scalars.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Scalars/Thms.lean)
for the arithmetic and Boolean handoff. The namespace is
`Silmaril.Logic.Temporal.TLA.Data.Tagged`.

## Carrier and sets

`Value` wraps a Mathlib `ZFSet` code. Recognized constructors encode distinct
kind tags as the first component of an internal Kuratowski pair. The
second component holds the payload. Lean equality is equality of codes.
`Value.tagged_inj` identifies both components. Every code can occur as
an element and as an unbounded witness. All codes outside the recognized
constructors' images are opaque, including malformed scalar payloads. Use the
checked `asSet`, `asInt` and `asBool` projections when recognizing values.

A set wraps a payload containing value codes. `Value.mem x s` holds only
when `s` is the encoding of a set whose payload contains the code of `x`.
`Value.set_eq_iff` proves extensional equality for such sets.
`SetData.mem_enum`, `mem_sep` and `mem_image` characterize enumeration,
separation and bounded image. The powerset maps each subset of the payload
back to a tagged set. `mem_powerset` therefore quantifies over exact subsets
and guarantees that each member is a set value. Range formation uses the
small type of members of a specific Mathlib set. `exists_not_mem` gives
a value outside each set.

This is a tagged interpretation of the set operations on set inputs.
The earlier [pure-set `Data.Model`](tla-data.md) requires membership and
extensionality on every value, as in §16.1.6. Tagged membership and
set-only extensionality are a distinct interface. In particular, the raw
payload membership of an integer code gives no language-level members of
that integer. A future evaluator must choose how to interpret set
operations applied to values that fail the set projection. The generic
`ChoicePolicy` can already be used on this carrier. Bounded quantifiers
range over `SetData.mem` and unbounded quantifiers can range over `Value`,
including opaque values. [Book §§6.1–6.2 and 16.1.6](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=317)
· [Pinned Mathlib set construction](https://github.com/leanprover/downstream-lean4/blob/569134c2fc750d92baa85d50cd925a7e20a93dd2/mathlib4/Mathlib/SetTheory/ZFC/Basic.lean)

## Scalar handoff

| Reference | Checked Lean interface |
| --- | --- |
| §§16.1.11, 18.4, Figs. 18.4–18.7 | `Value.integer` injects Lean integers. `SetData.integers` and `SetData.naturals` have exact membership laws on the whole carrier in `mem_integers` and `mem_naturals`. They contain the images of the infinite `Int` and `Nat` carriers. Naturals use the same representation as nonnegative integers. [Numbers](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=362) |
| §18.4, Figs. 18.5b–18.7 | `add_integer`, `modulo_integer`, `le_integer`, and `lt_integer` identify the typed operand results with Lean operations. Modulus takes a positive divisor for the checked arithmetic equation. `interval_integer` and `integer_mem_intRange` give the closed integer interval, empty when the lower endpoint exceeds the upper endpoint. The ordered comparison also satisfies `le_self` for every value. [Arithmetic and interval](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=365) |
| §§16.1.1, 16.1.3 | `Value.boolean` is injective and disjoint from the integer and set embeddings. `SetData.mem_booleans` characterizes the two Boolean values. `isTrue` tests equality with true, `ofProp` reifies a proposition, and `neg_boolean` and `and_boolean` give the Boolean tables. These connectives use the liberal interpretation. [Boolean interpretations](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=314) |

Fix one `Unspecified` function of the operation and operands across
valuations and steps. It is used for unsupported operand shapes in the
numeric slice and for nonpositive modulus divisors. It is independent of
`CHOOSE`'s no-witness policy. This slice does not model ProtoReals or
claim that the book leaves all of these inputs unconstrained in every
module. Native source resolution, prime, function graph operations and
the interpretation of function-derived tuples, records and strings are
separate layers.

The [examples](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Scalars/Examples.lean)
cover membership for numerals, intervals, signed integers and mixed
enumerations, including arithmetic used by HourClock. The definitions
are mathematical and use classical choice. All proof dependencies are
within the [repository axiom policy](../../policy.toml).
