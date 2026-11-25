# Starlark lexical calls

The core dialect follows the Bazel team's specification at revision
`c0af0ea03dc90d3bbc021394b693e6957cc15030`, with raw `spec.md` SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Functions][functions] · [Name binding][names] · [Definitions][defs]

## Resolved input

`Silmaril.Languages.Starlark.Functions.Thms` exposes function definitions,
calls, sequencing, conditionals, call-aware loops and the existing total
collection suites. Calls in expression position lower to calls
with fresh destination slots. The current collection suites can be lifted as
single blocks, including their local loops, writes and returns. Lifting
preserves the collection denotation exactly. This normalized input requires a
finite declaration table. The caller supplies statically resolved names and
scope legality, including full lists of local slots and free names.
[Definitions](../../Silmaril/Languages/Starlark/Functions/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Functions/Thms.lean)

Each invocation allocates its own lexical slots. A closure keeps the
addresses of free slots from its defining activation or module. It can
therefore observe later assignments to those slots, even after that activation
returns. The callee's capture slots are read-only, and assigning a local does
not rebind an outer scope. Slot tables and bindings return to the caller on
success and failure. Heap effects survive both exits. Functions with no
explicit return yield `None`. The shared heap keeps function identities and
uses those identities for function keys.
[Functions][functions] · [Definition and invocation primitives](../../Silmaril/Languages/Starlark/Functions/Defs.lean)

Freezing follows local captured cells, including a function stored in its
own captured slot. Defining-module globals are distinct from local captures.
The pinned Go implementation freezes them at module publication; a standalone
function freeze follows its local captures. The host boundary must supply
global roots when publishing a module.
[Module execution][modules] · [Pinned Go runtime][go-function]

## Termination and observations

A function's declaration index is stable across its closure instances.
An invocation rejects any declaration that is active already, even through a
different closure instance. Recursion detection precedes parameter binding.
The entry point starts with all declarations available. Descent removes every
matching declaration from the available set, while sequencing and branching
descend into smaller syntax. The underlying collection loops use finite
snapshots. There is no fuel or resource error in this profile. It assumes a
fixed finite declaration table and omits host callbacks and options enabling
recursion. A later semantics with such callbacks or options needs a separate
account of divergence and host observations.
[Denotation](../../Silmaril/Languages/Starlark/Functions/Denotation/Defs.lean) · [Recursion][functions]

The independent big-step rules compose collection-expression and suite
judgments with call entry and exit. The adequacy theorem covers exact results,
errors, caller restoration and the remaining shared store. Frames and heap
addresses are internal to the Lean model. The Go checks observe values,
aliasing, recursion rejection and heap effects through the host API.
[Operational rules](../../Silmaril/Languages/Starlark/Functions/Operational/Defs.lean)

## Argument binding

A resolved signature has positional-or-named parameters, keyword-only
parameters, and optional `*args` and `**kwargs` slots. Default expressions
evaluate left to right in the defining activation. Each new closure stores
their values once, and publication freezes them through the same heap
reachability rules as captured cells. Filling an omitted argument uses the
stored value, so mutable defaults share identity across calls.

The resolved call form represents positions, named operands, at most one
`*`, and at most one final `**`. All operand expressions evaluate left to right
before expansion. The supported `*` sources are lists, tuples and dictionary
keys. The supported `**` source is a dictionary with string keys. Expansion
preserves dictionary insertion order. When both expansions are invalid the
Go profile checks `**` first, after both operand expressions have run. A
call checks re-entry before binding parameters.

Binding checks positional overflow, assigns keywords in appearance order,
and fills omitted parameters from defaults. It reports duplicate assignment,
unexpected keywords and the missing required names. Fresh tuple and
dictionary packs are allocated only after successful binding. They enter
the activation by reference just like the other argument values. String
values support literal content, truth and key comparison in this profile.
Other string operations and additional star iterables remain open.

`runChecked` validates all normalized parameter lists and call sites before
executing, including unreachable call sites. It rejects duplicate parameter
names and repeated explicit keywords. The ordering of positional parameters
and expansion sites is enforced by their representation. A required
positional parameter cannot follow one with a default. The pinned prose
requires an optional keyword-only parameter after a bare `*`. The pinned
Go implementation accepts a required-only keyword signature, which the
fixture records as a difference. The caller still supplies lexical resolution
and valid identifier spellings, and lowers call expressions within operands
to ordered calls and temporary slots.
[Argument binding](../../Silmaril/Languages/Starlark/Functions/Arguments/Defs.lean) · [Functions][functions] · [Definitions][defs]

## Calls inside loops

`Body.forIn` accepts a resolved list, tuple or dictionary operand and a
call-aware body. It uses the finite snapshot, guards and outcome handling
of the collection suite. Each iteration writes its target binding before
running that body. A callee shares heap identities and active iterators
with its caller, so it cannot mutate a list or dictionary being traversed,
even through a separate alias. An inner loop releases its own guard.
The enclosing guard survives until its loop exits, including on an early
return or error.

`runChecked` checks break and continue in each declaration's own lexical
loop context, including unreachable code. The rules for loop entry and
iteration are part of `exec_iff_denoteBody`, which still accounts for
the exact outcome and store. The finite list of items bounds iteration
and the available declaration set bounds live calls.
[Collection loops](starlark-lists.md#iteration-and-control) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/LoopChecks.lean)

## Nested expression lowering

`Lowering.lower` compiles a resolved tree of call-free atoms, nested calls,
conditional expressions and operand-valued `and` and `or` to a `Body`
and a list of scratch slots. It stages the callee and every operand,
including call-free operands, before the final call. Positional, keyword,
`*` and `**` operands stay in source order. Expansion and argument errors
still use the call semantics. The compiler places branch work inside the
selected branch and skips its destination write if the operand fails.

Use the frame's direct bindings for scratch names when comparing exact
heaps. In this mode, omit the compiler scratch names from the heap-backed
slot map. They use a prefix outside the source identifier grammar. Thread
the returned `next` value into further lowering in the same frame to keep
ranges disjoint. The emitted code can be placed inside a function loop.

`lower_preserves` relates an independent source evaluation to
`denoteBody` of the emitted code. The proved fragment includes call-free
atoms, nested calls with positional, keyword, `*` and `**` operands,
conditionals and short-circuit operations. The source rules evaluate the
callee first, then operands left to right, stopping at the first evaluation
error. Only after all operands succeed do they expand the mapping and then
the iterable. This validation order follows the pinned Go implementation.
The rules share the value-level expansion and binding primitives and use
the operational rules for built-in invocation and core closure bodies.

Success writes the source value to the destination. An operand, expansion,
binding or callee error skips that write and retains the effects that
preceded the error. The projection keeps the entire heap,
active iterators, lexical slots and every visible binding, hiding only
direct scratch bindings. Source atoms cannot read scratch names. The host
supplies a visible, writable destination to observe the returned value.
Lean and pinned Go fixtures cover a failing nested keyword operand,
competing expansion errors and a duplicate keyword introduced by `**`.

Calls inside collection display and subscript atoms, default-expression
lowering and module-level expression lowering remain open. Static
validation of repeated explicit keywords stays with `runChecked`.
Supported iterable, mapping and callable values are those of the
shared-store call profile above.
[Preservation theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean) · [Independent source rules](../../Silmaril/Languages/Starlark/Functions/Lowering/Source/Defs.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/PreservationChecks.lean) · [Go fixtures](../../examples/starlark/nested-expressions/check.go)

## Resolving a normalized expression

`Lowering.Resolve.resolve` takes an unresolved expression and a lexical
context collected by the caller. It accepts integer and string literals,
identifier reads, calls with all four operand classes, conditionals and
operand-valued `and` and `or`. It uses the scalar resolver's precedence
for locals, globals and universal constants, then looks up the supported
built-ins. A declared local shadows a built-in even if the local has no
runtime value.

Pass the resolved tree to `Lowering.lower` and the resulting code to
`runChecked` with a destination outside the compiler scratch namespace.
Resolution rejects unknown names in all branches and reserves the
compiler's dollar prefix. Unary and binary operator nodes submitted
through the scalar AST get explicit profile errors. The checked executor
rejects repeated explicit keywords before evaluation, including in skipped
branches. The Lean fixture starts with unresolved names and observes the
result in the shared store. The pinned Go fixture checks equivalent
Starlark text.

This entry point takes normalized AST input and relies on the caller for
valid identifier tokens, the set of lexical bindings and allocated frame
slots. Text parsing, source locations, automatic scope collection for
call-aware blocks, and collection, subscript and attribute syntax remain
outside this adapter. The preservation theorem starts at the resulting
resolved tree.
[Resolver](../../Silmaril/Languages/Starlark/Functions/Lowering/Resolve/Defs.lean) · [End-to-end Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/Resolve/Checks.lean)

## Checks and extensions

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Checks \
  +Silmaril.Languages.Starlark.Functions.Arguments.Checks \
  +Silmaril.Languages.Starlark.Functions.LoopChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.PreservationChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/functions/check.go" && go run "$fixtures/call-loops/check.go" \
  && go run "$fixtures/nested-expressions/check.go")
```

Module initialization, prepublished imports and five universal built-ins
extend this profile. Host callable effects remain open.
[Modules](starlark-modules.md) · [Built-ins](starlark-builtins.md)


[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[defs]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[go-function]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go
