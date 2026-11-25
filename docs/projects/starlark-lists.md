# Starlark list store

The list slice follows the same Bazel-team core dialect as the scalar API,
at specification commit `c0af0ea03dc90d3bbc021394b693e6957cc15030` (2026-02-06).
The SHA-256 of the raw `spec.md` is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
The relevant sections cover list construction and append, identity and mutation,
subscripts, assignment order, and freezing at module publication.
[Specification][spec] · [Lists][lists] · [Identity][identity] · [Subscripts][index] · [Assignments][assign] · [Freezing][freeze]

## Entry points and observations

`Silmaril.Languages.Starlark.Lists.Thms` exposes the resolved code and store,
the executable denotation, and the relational rules. Expressions cover scalar
values, binding reads, list displays with arbitrary nesting, subscripts, and
one resolved method call, `append`. Suites cover name and subscript assignment,
expression statements, `pass`, and sequencing. Clients supply resolved bindings
and enforce source restrictions such as single-assignment globals. The scalar
entry points and theorem signatures from #2144 remain source-compatible.
[Code and store](../../Silmaril/Languages/Starlark/Lists/Defs.lean) · [Scalar API](starlark.md)

An allocated list has a fresh natural address in a single heap.
Copying a value copies its reference. Updates replace a cell at its original
address and every alias sees the new contents. Address numbers are internal
to a particular heap. An agreement theorem should relate heaps by a
correspondence of reachable addresses and compare aliasing through reads and
mutations. List equality is a separate language feature.

Indexing accepts integers in `[-length, length)`, with a negative index
measured from the end. Reads of frozen lists work normally. A mutation through
any alias fails once the cell is frozen. List display operands evaluate left
to right. Indexed assignment evaluates its RHS before its receiver and index.
`append` selects the method on its receiver before evaluating the argument
and checks mutability after argument evaluation. Its successful value is
Starlark `None`. The outcome preserves the state reached at the first error,
including effects of earlier operands. Error tags describe the failure kind
and may include the index, length, address, or binding. Diagnostic text and
backtraces are outside this observation. A dangling address is a model error
for reads or writes in malformed host-supplied state. The resolved code has no
raw address literal.
[Denotation](../../Silmaril/Languages/Starlark/Lists/Denotation/Defs.lean)

## Reachable freezing

`State.freeze` is a host operation supplied with root values. It represents the
freezing part of publication. Module initialization and root selection are
outside this API. A live list cell is reachable if it is a root or if a
reachable list cell contains a reference to it. The implementation marks from
these roots and visits each selected address at most once. Nested lists,
repeated references, self-cycles and cycles across multiple cells all use the
same reachability policy. Allocated addresses, bindings and the contents of
every cell are preserved during freezing. Previously frozen cells stay frozen and
unreachable mutable cells stay mutable.
[Freeze definitions](../../Silmaril/Languages/Starlark/Lists/Freeze/Defs.lean)

`eval_iff_denote` proves agreement between the big-step rules and the denotation
on the exact value or error and terminal state. The rules share the scalar and
heap primitives with the denotation and state their own operand ordering.
`freezes_iff_freeze` independently characterizes the host operation by the
live reachability relation and a pointwise update on the original heap. It
applies to every finite list heap and uses no bound on depth or acyclicity
assumption. `updateCell_frozen` proves that validated edits fail on a frozen
cell with the incoming state intact. These are theorems about the resolved
list model.
[Operational rules](../../Silmaril/Languages/Starlark/Lists/Operational/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

## Reproduction

Run the scalar and collection checks with the pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Languages.Starlark.Checks +Silmaril.Languages.Starlark.Lists.Checks
```

The kernel-checked collection cases cover fresh and shared addresses, negative
and ill-typed indexes, error order and state retention, transitive freeze,
self-cycles and mutual cycles, and mutation attempts through frozen aliases.
The corresponding Go checks use `Program.Init` to observe source evaluation
before publication, then call the host's `Freeze` on a selected root. The
reference is starlark-go at commit `4f4267fb140d1e8b91c9bce55cee2f809e8840dd`
with the default syntax options. The huge-index case compares failure only
because the Go implementation reports its 32-bit index conversion limit.
[Lean fixtures](../../Silmaril/Languages/Starlark/Lists/Checks.lean) · [Go fixtures](../../examples/starlark/list-store/check.go) · [Pinned oracle][go]

Run the reference fixture from the public oracle checkout using Go 1.25 or
newer. Start these commands from the Silmaril repository root.

```sh
fixture="$(pwd)/examples/starlark/list-store/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

## Remaining work

- **Iteration.** Add resolved function-body `for` over a list, loop-target
  binding, `break` and `continue`. Track active iterators by heap address so
  both mutation primitives can enforce the restriction through aliases.
  Prove iterator release on normal completion, loop exit and error. Extend
  the same discipline to later return and comprehension rules. This is the
  next list-store increment. [Iteration][iteration]
- **Collection operations and keys.** List equality and ordering, truth,
  length, concatenation, slicing, comprehensions, augmented assignment, and
  the other list methods remain open. Add tuple and dict cells at addresses
  in the same heap. Tuples have immutable fields and can reach mutable cells.
  A dict reaches its keys and values, with a separate insertion-order policy.
  Key admissibility needs type-specific hashability and stable hashes. The
  pinned Lists section and Go implementation rule out list keys even after
  freezing. Tuple keys need admissible elements recursively. Freezing alone
  grants no blanket permission to use a value as a key.
  [Lists][lists] · [Hashing][hashing]
- **Calls and closures.** Pass list references by value into the callee's
  lexical frame with the same heap. Add stored closure roots for captured
  cells and defaults so freezing reaches their contents, and give closure
  declarations their own identity and recursion checks. The current method
  primitive covers the one-argument list `append` call.
  [Functions][functions] · [Identity][identity]
- **Module initialization and loading.** Give each module a lexical frame
  and run its body with its own thread context. Publish only after success
  and freezing all of its global roots, including private globals. The
  loader cache must preserve the published identities when bindings are
  imported by another module. The loader still needs export validation,
  dependency and failure behavior, and a host policy for effects and cache
  keys. [Module execution][modules] · [Load statements][loading]

[spec]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md
[lists]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#lists
[identity]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#identity-and-mutation
[index]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#subscript-expressions
[assign]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#assignments
[freeze]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#freezing-a-value
[iteration]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#iteration
[hashing]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#hashing
[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
