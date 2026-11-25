# CBV L2 denotations

These denotations follow Peter Sewell’s Cambridge Part IB *Semantics of
Programming Languages* notes for 2025–26, dated 12 February 2026. They use
the CBV application rules on p. 55, strict `let` on p. 60, recursion on
p. 61, and the collected definition on pp. 65–67. The PDF
matches the SHA-256 for `sewell2026semantics`. [Notes][notes] · [Bibliography][bib]

```sh
lake build --wfail +Silmaril.Courses.Cambridge.L2.Denotational
```

## Pure fragment

`L2.PureDenotation.Term Γ e T` is a computational typing derivation for a
fragment of the existing `L2.Expr` AST. It admits integers, Booleans,
`skip`, addition, comparison, conditionals, sequencing, bound variables,
lambdas, application, and strict nonrecursive `let`. Its environment
contains one semantic value per bound variable, with the nearest
binder first. A lambda denotes a function that closes over this
environment. Application supplies the argument's denotation to that
function. The fragment has no free names, store operations, loops, or
recursive bindings.

| Lean result | Contract |
| --- | --- |
| `Term.hasType`, `Term.scoped`, `Term.closed` | The derivation embeds in L2 typing, has the indexed binder depth, and is closed at an empty environment. |
| `Term.adequate` | For a closed fragment term at `int`, `bool`, or `unit`, a finite L2 run ends in a value iff its result is the quoted denotation paired with the original store. |
| `Term.terminates`, `Term.not_diverges` | Every closed derivation has a finite CBV evaluation to a value and admits no infinite CBV trace. This includes functions. |

The proof relates semantic functions to substitution-based lambda values by
their behavior on related arguments. The beta calculation extends the
substitution that represents the saved environment. The two examples on
slide 140 return `12` and `6`. A separate strict-let example checks
lexical scope by shadowing a name after a closure has captured it.

## Mutable-store fragment

`L2.EffectfulDenotation.Term locations Γ e T` adds dereference and
assignment at locations declared in the existing L2 typing environment.
It interprets a computation as `StateT Store Part A`. A function value
maps an argument to a computation. The closure saves its lexical
environment. Application evaluates the function expression and then the
argument, threading the store through both before running the closure in
the resulting store. Assignment updates an existing location after
evaluating its right-hand side, as in the collected L2 rules.

| Lean result | Contract |
| --- | --- |
| `Term.hasType`, `Term.scoped`, `Term.closed` | Each derivation embeds in L2 typing and has the indexed binder depth. An empty lexical environment gives a closed expression. |
| `Term.terminates` | Every closed derivation, including at function types, reaches an L2 value from a store covering the declared locations. |
| `Term.adequate` | For a closed derivation at `int`, `bool`, or `unit` and a covering initial store, a configuration belongs to the denotational observation iff the existing substitution-based small-step semantics reaches it with a value. Both observations include the entire final store. |
| `sat_iff` | On the same admitted sources, atomic satisfaction agrees with `L2.OperationalInstitution.semantics.May` for the corresponding `.returned` configuration. |

The function clause of the adequacy relation quantifies over related
arguments and covering stores. The evaluation proof uses
`Step.preserves_coverage` to pass the store hypothesis along the
constructed reduction. The institutional comparison concerns finite
ground returns on these sources.

Slide 138's argument writes `2` before the body writes `1`. Its
denotation and institutional observation both return `skip` with
`l ↦ 1`. The lexical-capture example saves `!l = 3`, writes `5` in
the function operand, and increments the location to `7` in the
argument. The body adds the saved `3` to the current `7`, returning
`10` with `l ↦ 7`.

## Recursive functions and loops

`L2.RelationalDenotation.Returns ρ e s v t` relates the lexical
environment, expression and initial store to a semantic value and final
store. Its inductive rules generate the least relation closed under the
evaluation clauses. A function call evaluates both operands in order and
uses the store after the argument. A recursive closure saves its definition
environment. The call evaluates the body with the parameter and the same
recursive closure at the front of that environment. The while rules run
the guard before the body and retain the store of the final false guard.

| Lean result | Contract |
| --- | --- |
| `Returns.while_iff` | A loop returns after a finite sequence of true guard/body iterations and a false guard. Every iteration passes its resulting store to the next. |
| `adequate_env` | A finite return with an explicit lexical environment agrees exactly with L2 substitution small-step on the expression instantiated with that environment, including the quoted result and full final store. |
| `adequate`, `sat_iff` | The empty-environment case gives finite-return adequacy for the original L2 expression and agrees with the institution's `.returned` observation. This includes function results quoted as L2 lambda values. |
| `agrees_effectful` | The relational model and the typed `StateT Store Part` model agree on ground results for the earlier fragment and covering stores. |

The adequacy proof factors a finite small-step path by expression
constructor. It uses the existing `Expr.recClosure` substitution rule
to reify recursive closures. The environment supplies de Bruijn indices
in nearest-first order. Indices beyond the environment remain ambient
indices after substitution, and free names stay free. An unbound variable
has no evaluation rule. The theorem applies as stated to arbitrary stores
and syntax, including ill-typed expressions. The closed, well-typed course
programs use an empty lexical environment and a store covering their
declared locations.

The observations record successful returns only. Operationally, a missing
location can be stuck and a loop can have an infinite trace. Both have an
empty finite-return observation, as the checked examples show. Other
examples check a recursive call that captures `3` and later returns `13`
with `l ↦ 13`, and a loop whose final false guard writes `l ↦ 3`.

## Chapter 4 coverage

| Pinned material | Denotation coverage |
| --- | --- |
| CBV application and typing, §§4.2–4.3 | Checked in both fragments for the represented ground and function types. |
| Strict local definitions, §4.4, p. 60 | Checked in both fragments. |
| Integer store operations and inherited CBV rules, §4.6, pp. 65–67 | Checked in the mutable-store fragment for lookup, assignment, sequencing, conditionals, addition and comparison. |
| Recursive functions, §4.4, p. 61 | Finite adequate environment semantics for recursive binding, application and returning a recursive closure. |
| While, §4.6, p. 66 | Finite adequate relational iteration with store effects in guards and bodies. |
| Stuckness and infinite evaluation | Separate operational predicates. The relational denotation observes successful finite returns. |
| Call by name and unrestricted reduction, §4.2 | Outside the CBV denotations. |

[Recursive-function rules][recursion] · [L1’s Elgot state interpretation][l1]

[notes]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=55
[recursion]: https://www.cl.cam.ac.uk/teaching/2526/Semantics/notes.pdf#page=61
[bib]: ../../references.bib
[l1]: cambridge-denotational.md#effectful-l1
