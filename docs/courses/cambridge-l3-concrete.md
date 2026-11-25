# Cambridge L3 concrete syntax

Import `Silmaril.Courses.Cambridge.L3.Concrete` to parse and print L3 terms
and types from Peter Sewell’s 12 February 2026 notes. The byte profile covers
the constructors of the collected definition. It shares the
[L1/L2 UTF-8 and tokenization rules](cambridge-concrete.md), including a
virtual outer group and explicit grouping for nested infix and binding
forms. Ordinary ungrouped precedence syntax where the course specifies it
remains a follow-up for all three languages.
[Sewell, §5.5, pp. 78–82](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)

## Grammar

The whole input is one group body. A parenthesized body is one term or type
inside a larger production. Records and the unary term forms `!`, `ref`,
`fst` and `snd` can also occur directly as operands. Group projection
before using it as an operand, for example `fst (r.p)`.

```text
type       ::= int | bool | unit | ( type-body ) | { type-fields }
type-body  ::= type | type → type | type ∗ type | type + type | type ref
type-field ::= label : type

term       ::= numeral | minus numeral | true | false | skip | variable
             | location | ! term | ref term | fst term | snd term
             | ( term-body ) | { term-fields }
term-body  ::= term
             | term + term | term ≥ term | term ; term | term := term
             | if term then term else term | while term do term done
             | term term | fun variable : type → term
             | let variable : type = term in term
             | let rec variable : type → type =
                 ( fun variable : type → term ) in term
             | term , term | term . label
             | inl term : type | inr term : type
             | match term with inl ( variable : type ) → term
                 | inr ( variable : type ) → term
term-field ::= label = term
```

Each field list can be empty. Nonempty lists are comma-separated, with
distinct labels and no trailing comma. The parser preserves order and builds
the course AST’s `RecordLabels` witness. In `let rec`, the two parameter
type annotations must agree as parsed types, including the order of any
record fields. `*` is an ASCII alias for `∗`.

Variables and labels use the shared identifier spelling and are distinguished
by grammatical position. L3 additionally reserves `fst`, `snd`, `ref`,
`inl`, `inr`, `match` and `with`. Earlier languages still allow these names.
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

The canonical printers take `SourceExpr` or `SourceType`, whose names have
a spelling in the source vocabulary. They preserve record order and all
binder names. `parse_print` and `parseType_printType` recover the original
ASTs. `print_injective` and `printType_injective` follow from those
round-trips. `parseResolved_print` gives the corresponding resolved
expression.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L3.Concrete \
  +Silmaril.Courses.Cambridge.L3.Concrete.Examples
```

The [byte regressions](../../Silmaril/Courses/Cambridge/L3/Concrete/Examples.lean)
cover dependent record order, duplicate labels, nested products and sums,
location syntax, mutation and allocation, scope resolution, canonical
printing and malformed input.
