# Python module-entry source profile

The source checker reads the actual module scope analysis and retains a
typed global reference for each read and write. Readers and assignment
targets carry their name and exact access, including an explicit
`global` declaration. An uninitialized name read still carries its key so
the runtime can give the defined lookup outcome.

The plan contains single-name assignments and assertions in source order.
Operands include signed integers, booleans, global reads, addition, floor
division and a single equality comparison. Bare `global` and `pass`
provide the corresponding scope and statement evidence. The plan supplies
operations to the module runtime, which gives the initialized store and
execution outcomes.
[Definitions and translation laws](../../Silmaril/Languages/Python/Compile/ModuleEntry/Thms.lean)

A list or tuple of signed integer literals can be indexed by a signed
integer literal. The checker adjusts a negative index once by the
sequence length and lowers a successful lookup to an integer operand.
All elements must be integer literals. Out-of-bounds indices, slices,
and dynamic receivers or indices are outside the profile.

Module `if` statements admit Boolean and signed integer literal guards.
Both arms must consist of single-name assignments, message-free assertions
and `pass`, with every operand checked by the scalar profile. Scope analysis
visits the entire statement before this check. Declarations, nested scopes,
and other statement forms in either arm prevent elision.

The translation certifies the decoded truth value and both arms, and emits
the selected actions in source order before the remaining module.
Literal Boolean assertions in an arm lower to the equivalent integer truth
tests. Both runners use their existing transitions, preserving writes before
a failing assertion or lookup and skipping later statements on failure.

Scalar conditional expressions accept the same literal guards. The checker
validates both operands in the analyzed module scope and emits only the
selected operand. A selected Boolean literal uses the existing Boolean
result of equality with `True`. The resulting value retains its Boolean
type in ordinary and seeded execution. Other operands keep their existing
value and failure semantics. The unselected operand performs no lookup.

The scalar checker folds single tuple equality and membership comparisons
over flat tuples of exact Boolean or signed integer literals. Equality uses
the tuple lengths and corresponding scalar values. Membership tests tuple
elements in order using the same scalar equality, including Boolean and
integer equality at zero and one. The checked operand emits a Boolean
through scalar equality and performs no runtime lookup or allocation.

The regression emits Lean from Python source and verifies the global
access witnesses, action order and the diagnostic for an assertion
message.

The source runner accepts an initial namespace and builds the Core module
entry using the analyzed spelling of each name. Its correspondence law
matches the exact completion, visible trace and residual namespace.
The execution regression compares CPython and Lean on initialized reads,
overwrites, assertion failure, an unbound read and arithmetic failure.
[Runner contract](../../Silmaril/Languages/Python/Compile/ModuleEntry/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Thms
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Run.Thms
```

## Function bindings and calls

The function plan keeps the source order of top-level assignments,
definitions and calls. A definition carries its analyzed child path,
fixed positional destinations and lowered body. Each call reads the
function by its module name and supplies ordered positional operands. The
result can be assigned to a name, discarded or tested by a message-free
assertion.

An implicit or declared global read in a function body retains its module
name. This supplies lookup in the namespace at call time, including writes
between a definition and call. Local references continue to use bounded
frame slots. The regression verifies both kinds of lookup.
[Function plan](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Thms
```

The module function runner links the selected bodies and publishes them in
the shared Core namespace, in source order. A positional call reads its
callable and its literal or name arguments through that namespace.
Positional arguments at a module call site may also be direct named calls
with literal or name operands. The ordinary runner saves the outer
callable in a frame local, evaluates each argument once from left to right
into separate locals, then invokes the saved callable. The result updates
the selected binding only on successful completion. The runner gives the
labelled invocation trace and a residual state that can be resumed with
further fuel. Its prefix composition theorem agrees with
a run using the combined fuel.

The adjacent keyword discard profile checks a bare call immediately
after its undecorated function definition. The definition has one required
positional-or-keyword parameter without an annotation. The call has one
`**` mapping literal with one string key and one integer literal value.
The key must equal the parameter's code points. The typed plan records
the adjacent publication and the one-slot argument mapping. The runtime
reads the live function binding and invokes it through the ordinary
positional executor with that integer. The seeded selector requires a
published function with one slot and records the ordinary completion
and reached heap. The call's result is discarded.

Deeper argument nesting, arithmetic call operands, and keyword or
unpacked arguments outside the adjacent discard shape are rejected. The seeded runner supports these
nested instructions within its [closed call profile](python-seeded-module-runner.md).
The CPython regression checks
result placement, lookup and argument error order, and residual bindings.
The Lean regression also checks the call-entry order across a live prefix.
The ordinary module runner also accepts a message-free `assert not test`
when `test` is an existing module operand. It evaluates the operand once,
propagates evaluation errors, and succeeds exactly when the result is
false by the ordinary truth rule. This includes a name bound to a
returned `None`. The seeded runner also handles this instruction for
its existing [seeded operands](python-seeded-module-runner.md).
[Module-call runner](../../Silmaril/Languages/Python/Compile/ModuleEntry/Functions/Run/Thms.lean)

```sh
make check CHECK_TARGETS=+Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Thms
```
