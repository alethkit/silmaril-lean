# Cambridge L3 concrete syntax

Import `Silmaril.Courses.Cambridge.L3.Concrete` to parse and print L3 terms
and types from Peter Sewell’s 12 February 2026 notes. The byte profile covers
the constructors of the collected definition and extends the
[L1/L2 UTF-8 and precedence rules](cambridge-concrete.md). Application
associates left, arrows associate right, and lambda bodies extend to the
enclosing delimiter as in L2.
[Sewell, pp. 49, 69–75 and 78–82](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)

## Terms and types

The tightest term levels are atom, prefix operators (`!`, `ref`, `fst`,
`snd`), field projection and application, in that order. Projections chain
on the left, so `r.p.q` means `(r.p).q`. Group an operand to change the
binding. For example, `fst (r.p)` applies `fst` to the field. The precedence of
prefix operators over projection preserves the existing grouped spelling
of `(fst r . p)` as a projection. The notes leave the relative binding of
these operators open.

Addition, comparison, assignment and sequence have the same levels as in
L1/L2. L3 accepts an expression as the assignment target and as the operand
of dereference. Parentheses are part of pair notation `(left, right)`.
A pair may contain compound ungrouped operands and nesting requires a
separate pair at each level. The comma also separates fields within braces.

An injection has the form `inl term : type` or `inr term : type`. The colon
ends the payload and introduces a full type. A match uses
`match term with inl (x : type) → left | inr (y : type) → right`.
The branch binder parentheses and the bar delimit the annotated binders
and the first branch. The final branch extends to the enclosing delimiter.
Group an injection or match when using the whole expression as an
application argument. The binding of these forms next to other operators
is a parser convention.

Type precedence, from tightest to loosest, is atom (including records),
postfix `ref`, product `∗`, sum `+`, and arrow `→`. Postfix `ref` may repeat.
An unparenthesized product chain such as `int ∗ int ∗ int` is excluded by
the notes (p. 69). This parser also requires grouping for nested sums.
The relative levels for products, sums and references, and the grouping
requirement for nested sums, are parser conventions.

Each field list can be empty. Nonempty lists are comma-separated, with
distinct labels and no trailing comma. The parser preserves order and builds
the course AST’s `RecordLabels` witness. In `let rec`, the two parameter
type annotations must agree as parsed types, including the order of any
record fields. `*` is an ASCII alias for `∗`.

The original parser uses the same ASCII spelling rule for variables and
labels, with grammatical position selecting the role. Use `Exact.parse`
for the notes' separate spelling classes. L3 reserves
`fst`, `snd`, `ref`, `inl`, `inr`, `match` and `with`. Earlier languages
still allow these names.
The AST numbers the notes’ locations in the order `l`, `l0`, `l1`, and so on.
Numeric location suffixes use decimal without leading zeros. The term grammar
can read these literals. The separate course convention that whole programs
start with an empty store and create their own locations concerns execution.

## AST and byte contracts

`parse` returns the course’s named `L3.RawExpr`. `parseResolved` uses the
existing resolver, including independent payload binders in the two match
branches. De Bruijn indices and store configurations belong to the internal
model. `parseType` returns `L3.Ty`. The parsers consume the complete input.
Semantic typing and store invariants are still checked by the course
interfaces.

The public parser tries the explicitly grouped reader first and uses the
precedence reader on a miss. Both require complete input. The canonical
printers take `SourceExpr` or `SourceType`, whose names have a spelling in
the source vocabulary. They preserve record order and all
binder names. `parse_print` and `parseType_printType` recover the original
ASTs. `print_injective` and `printType_injective` follow from those
round-trips. `parseResolved_print` gives the corresponding resolved
expression.

## Separate variable and label classes

Section 5.2 (pp. 72–73) introduces the label class and explicitly
excludes `fun x:T → {x = 3}`. Section 5.5 (p. 78) gives separate sets
for variables and labels, illustrated by `x, y, z` and `p, q`.
It uses the label class for fields of record types, fields of record terms,
and projections. The variable class includes uses and all binders.
Membership is independent of scope. A label can appear in different
records, and the distinct-label rule still applies within each record.
[§5.2](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=72) ·
[§5.5](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=78)

The notes leave the full spelling sets open. Supply a fixed
`Exact.Classifier` for the vocabulary you want to read. It assigns
each identifier to exactly one class. The same choice applies to
standalone types, terms and every annotation, including those on
injections, match branches and recursive definitions. For example:

```lean
import Silmaril.Courses.Cambridge.L3.Concrete

open Silmaril.Courses.Cambridge.L3.Concrete

def exampleClasses : Exact.Classifier
  | "p" | "q" => .label
  | _ => .variable

#guard (Exact.parse exampleClasses "fun x:{p:int} → x.p".toUTF8).isSome
#guard (Exact.parse exampleClasses "(fun x:int → {x = 3})".toUTF8).isNone
#guard (Exact.parseType exampleClasses "{x:int}".toUTF8).isNone
```

`Exact.parse` and `Exact.parseType` apply the class check to the AST
returned by the existing full-input reader. `Exact.parseResolved`
then resolves the names. `Exact.parse_eq_some_iff` and
`Exact.parseType_eq_some_iff` state exactly how decoding depends on
the existing byte profile and the class check.

`Exact.SourceExpr` and `Exact.SourceType` are the canonical AST domains.
They require both the existing spelling rules and the chosen class at
each position. The printers emit the same grouped UTF-8 encoding.
`Exact.parse_print` and `Exact.parseType_printType` recover these
ASTs. `Exact.print_injective` and `Exact.printType_injective` prove
injectivity on the respective domains. The original `parse`, `parseType`
and their unconditional canonical theorems remain available.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L3.Concrete \
  +Silmaril.Courses.Cambridge.L3.Concrete.Examples
```

The [byte regressions](../../Silmaril/Courses/Cambridge/L3/Concrete/Examples.lean)
cover ordered records, duplicate labels, grouped products, precedence and
association, annotation and match boundaries, scope resolution, mutation
and allocation, canonical printing and malformed input.
