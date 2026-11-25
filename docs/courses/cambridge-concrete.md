# Cambridge L1 and L2 concrete syntax

`Silmaril.Courses.Cambridge.L1.Concrete` and
`Silmaril.Courses.Cambridge.L2.Concrete` parse and print a grouped UTF-8 source
profile of Peter Sewell’s 12 February 2026 Part IB notes. The term constructors
and types come from the collected definitions in §§2.3 and 4.6. The notes use
parentheses to disambiguate abstract syntax (§3.1). This profile requires
grouping for nested compound terms and types, so an infix or application
chain needs explicit grouping even where the notes give a precedence rule.
[Lecture notes, pp. 29–30, 35–36, 49–50 and 65–67](https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf)

## Lexical conventions

- The parser decodes the complete byte array as UTF-8 and rejects malformed
  input. ASCII space, tab, carriage return and newline delimit tokens.
  Comments and Unicode whitespace are outside this profile.
- A maximal word consists of ASCII letters, digits, underscores or
  apostrophes. Variables begin with an ASCII letter or underscore.
  Keywords and locations are reserved. A location is `l` followed by zero or
  more digits, with the spelling kept verbatim. A numeral is a nonempty
  sequence of decimal digits, with no digit separators. A minus token before
  a numeral denotes a negative integer. Integers are unbounded.
- The lexer recognizes punctuation adjacent to other tokens. `>=`, `->`
  and `-` are aliases for `≥`, `→` and `−`. The pairs `:=`, `>=` and
  `->` are single tokens when adjacent.

## Grammar and binding

A whole input is one group body. Parentheses make a group body into an
expression or type for use inside a larger production. Parenthesized atoms
and redundant groups are allowed.

```text
expr        ::= numeral | minus numeral | true | false | skip | ! location
              | variable                                    (L2)
              | ( group-body )
group-body  ::= expr
              | expr + expr | expr ≥ expr | expr ; expr
              | if expr then expr else expr
              | location := expr
              | while expr do expr done
              | expr expr                                   (L2)
              | fun variable : type → expr                   (L2)
              | let variable : type = expr in expr           (L2)
              | let rec variable : type → type =
                  ( fun variable : type → expr ) in expr    (L2)
type        ::= int | bool | unit | ( type-body )
type-body   ::= type | type → type                           (arrow in L2)
```

The repeated parameter annotation in `let rec` must agree with the domain
annotation. Any other typing or store conditions are checked separately.
`intref` is the notes’ location typing judgment vocabulary. Term type
annotations use the expression type grammar above.

For example, `while (!l0 ≥ 0) do (l0 := (!l0 + −1)) done` parses as L1.
`fun x : int → (x + 1)` parses as L2. Write `((f x) y)` for nested
application and `int → (bool → int)` for the corresponding arrow nesting
in a standalone type.

L1 `parse` returns `L1.Expr`. L2 `parse` returns `L2.RawExpr`, with
binder spellings intact. L2 `parseResolved` applies the existing
`RawExpr.resolve []` and retains free names. An ordinary `let` binds in its
body. A recursive function name binds in the function and the `in` body,
and its parameter binds in the function body. De Bruijn indices and the
resolved free-variable constructor are internal representations. Store
configurations also have no source production.

## Canonical bytes and checks

`print` takes a `SourceExpr`, an AST with names in the source vocabulary.
The internal ASTs retain unrestricted strings. The printer emits fully
grouped compound terms, the Unicode symbols above and one ASCII space between
tokens. `parse_print` recovers the original AST and `print_injective` proves
that equal canonical bytes imply equal source ASTs. `parseType_printType`
and `printType_injective` give the corresponding contracts for expression
types. L2 also proves `parseResolved_print`. Parsing discards whitespace and
grouping choices.

The shared tokenizer feeds an AST-directed parser with full-input checks.
L1 recursively restricts the shared result to the imperative fragment. Using
one production implementation keeps the shared L1/L2 syntax in sync.

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L1.Concrete \
  +Silmaril.Courses.Cambridge.L2.Concrete \
  +Silmaril.Courses.Cambridge.Concrete.Examples
```

[Byte regressions](../../Silmaril/Courses/Cambridge/Concrete/Examples.lean)
exercise both entry points on actual UTF-8 and malformed byte arrays. They
check grouping, token boundaries, binder resolution, recursive annotation
agreement, canonically printed text and rejection of L2 forms by L1.
