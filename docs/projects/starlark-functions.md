# Starlark lexical calls

The core dialect follows the Bazel team's specification at revision
`c0af0ea03dc90d3bbc021394b693e6957cc15030`, with raw `spec.md` SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Functions][functions] · [Name binding][names] · [Definitions][defs]

## Resolved input

`Silmaril.Languages.Starlark.Functions.Thms` exposes function definitions,
calls, native expression returns, assignments, tests and loop operands,
sequencing and the existing total collection suites. The current collection
suites can be lifted as single blocks, including their local loops, writes
and returns. Lifting preserves the collection denotation exactly. This normalized input requires a
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
parameters, and optional `*args` and `**kwargs` slots. `Parameter.defaultExpr`
holds an optional resolved expression. Existing call-free defaults embed
with `Lowering.Expr.atom`, which preserves their exact denotation.

Each `define` evaluates its defaults once in declaration order, with
positional defaults followed by keyword-only defaults. It uses the defining
frame and its current available-declaration set. Calls in defaults remove
their prepared declaration from that set on entry. A default error keeps
the state at failure, skips later defaults, and leaves the definition
target intact. When all defaults succeed, the closure installer stores the
values under their parameter slots. Invocation uses those saved values for
omitted arguments, so mutable defaults share identity across calls.
Publication follows the same reachability rules for stored defaults and
captured cells.

`exec_define_iff_denoteDefaults` compares the ordered direct denotation
with independent expression and closure-body derivations on the exact
result, frame and heap. The rules share closure installation and argument
binding with the executable core.
[Definition agreement](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Default fixtures](../../Silmaril/Languages/Starlark/Functions/NativeDefaultsChecks.lean)

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
executing, including calls in defaults and unreachable operands. It rejects
duplicate parameter names and repeated explicit keywords. The ordering of positional parameters
and expansion sites is enforced by their representation. A required
positional parameter cannot follow one with a default. The pinned prose
requires an optional keyword-only parameter after a bare `*`. The pinned
Go implementation accepts a required-only keyword signature, which the
fixture records as a difference. The caller still supplies lexical resolution
and valid identifier spellings, and lowers call expressions within operands
to ordered calls and temporary slots.
[Argument binding](../../Silmaril/Languages/Starlark/Functions/Arguments/Defs.lean) · [Functions][functions] · [Definitions][defs]

## Calls inside loops

`Body.forInExpr` evaluates a resolved iterable expression once in the
current frame. The operand may invoke a closure and mutate the collection
it returns. A successful operand supplies the value for the snapshot and
guard acquisition. An operand failure propagates its effects with
no loop target write or new guard.

`Body.forInExpr`, the call-free `Body.forIn`, and collection suites share
the same acquisition, finite snapshot and cleanup denotation for list,
tuple and dictionary operands. Each iteration writes its target binding
before running the body. A callee shares heap identities and active
iterators with its caller, so the guard covers mutations through aliases.
The loop restores the guard stack left by operand evaluation on every
exit, including return and error.

`runChecked` validates calls in the operand and checks break and continue
in each declaration's own lexical loop context, including unreachable
code. `exec_iff_denoteBody` covers the exact result or error, frame, heap
and iterator stack. The finite item list bounds iteration and the
available declaration set bounds live calls.
[Native loop agreement and cleanup](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Native loop fixtures](../../Silmaril/Languages/Starlark/Functions/NativeLoopChecks.lean) · [Collection loops](starlark-lists.md#iteration-and-control)

## Direct denotation of resolved expressions

`Lowering.denoteExpr` maps a resolved expression and state to a value or
dynamic error with its final state. It interprets call-free collection
atoms, nested calls with positional, keyword, `*` and `**` operands,
conditionals and operand-valued `and` and `or`. A call evaluates the callee
and operands from left to right, then expands and binds the arguments.
`**` validation precedes `*` validation in the pinned Go profile.
Expansion and binding use the same value-level primitives as the
operational rules.

Closure application invokes `denoteBody` under the reduced
available-declaration set. Built-ins use their denotation.
Caller bindings and slots are restored after a closure returns or fails,
and heap effects survive. This interpreter recurses on expression syntax
and finite operand lists. The core recurses on body syntax and the
available-declaration set. There is no fuel parameter.

`denoteExpr_eq_of_evaluates` proves exact equality with every operational
expression derivation. `evaluates_iff_denoteExpr` also constructs a
derivation for every denotational outcome when all atoms are admissible,
including atoms on skipped branches. Admissible atoms use call-free
collection code and keep compiler scratch names out of source reads.
The equality includes the entire heap, bindings, slots and iterator stack.
The direct interpreter has no destination or scratch-frame condition.
The separate lowering theorem accounts for destination assignment and
scratch projection when compiling the same expression.

[Denotation](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Defs.lean) · [Adequacy](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Closure fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Checks.lean) · [Coverage obligations](starlark.md#coverage-obligations)

## Native expression positions

`Body.returnExpr`, `Body.assignExpr`, `Body.branchExpr` and `Body.forInExpr`
evaluate a resolved expression in the current frame. A successful return operand produces the
return signal. Assignment writes its destination with the existing binding
semantics after the right-hand side succeeds. A successful test is converted
to truth and selects one body in the resulting state. An operand or truth
error propagates with its residual state.

`runChecked` validates explicit keyword names throughout each expression
and verifies loop control in both conditional bodies, including skipped
paths, before execution. The caller supplies resolved names and the frame.

Native positions and standalone expressions use the same executable
expression evaluator. It recurses over expression syntax. When it reaches
a closure, it calls `denoteBody` at a strictly smaller available-declaration
set. The prepared closure supplies a membership proof for the declaration
that is removed. All recursive body calls under the same declaration set
descend on body syntax. An active declaration is rejected as re-entry.

The operational rules share the `ExecExpr` judgment, which requires
operational derivations for invoked closure bodies. Soundness uses exact
agreement on those smaller calls. Adequacy constructs the expression and
closure derivations under the same descent. `exec_iff_denoteBody` compares
the exact result or error and final frame, heap and iterator stack. The
expression-position theorems in the denotation header expose that agreement
without the compiler's scratch projection.

Module commands still use the separate call-free atomic and
destination-based call forms. Collection displays and subscripts use
call-free atoms as well. The coverage guide records the remaining integration
obligations.
[Body rules](../../Silmaril/Languages/Starlark/Functions/Operational/Defs.lean) · [Native position agreement](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Assignment and conditional fixtures](../../Silmaril/Languages/Starlark/Functions/NativeBodyChecks.lean) · [Return fixtures](../../Silmaril/Languages/Starlark/Functions/NativeReturnChecks.lean) · [Coverage obligations](starlark.md#coverage-obligations)

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

Calls inside collection display and subscript atoms and native
module-level expression statements and assignment operands remain open. Static
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

## Quoting an expression in Lean

`starlark%[...]` constructs a `Lowering.Resolve.SourceExpr` in a Lean file.
It accepts grouped expressions, simple ASCII identifiers, decimal integer
literals with optional minus, plain double-quoted strings, nested calls,
conditionals and operand-valued `and` and `or`. Calls accept positional
and named arguments followed by optional `*` and `**`, with an optional
trailing comma. Quoted names are strings in the AST. The resolver still
uses the caller's Starlark lexical context.

```lean
module

import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs

open Silmaril.Languages.Starlark.Functions.Lowering
open scoped Silmaril.Languages.Starlark.Functions.Lowering.Quote

def exampleExpression : Resolve.SourceExpr :=
  starlark%[(len(*items, **keywords) or len(9)) if True else len(9)]
```

The quotation uses Lean's lexer. It rejects unsupported literal spellings,
list displays, subscripts, binary `+`, duplicate explicit keywords and
invalid argument ordering with source ranges. Other forms outside its
grammar get Lean parser diagnostics. Arbitrary Starlark text, statements,
the full identifier and string lexical grammar, and locations on resolver
errors remain outside this entry point. The quotation and resolver have
separate regression checks. The lowering preservation theorem continues
to start with a resolved expression.
[Quotation](../../Silmaril/Languages/Starlark/Functions/Lowering/Quote/Defs.lean) · [Quotation-to-execution and diagnostic fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/Quote/Checks.lean)

## Checks and extensions

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Checks \
  +Silmaril.Languages.Starlark.Functions.Arguments.Checks \
  +Silmaril.Languages.Starlark.Functions.NativeBodyChecks \
  +Silmaril.Languages.Starlark.Functions.NativeDefaultsChecks \
  +Silmaril.Languages.Starlark.Functions.NativeReturnChecks \
  +Silmaril.Languages.Starlark.Functions.NativeLoopChecks \
  +Silmaril.Languages.Starlark.Functions.LoopChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.PreservationChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Quote.Checks
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
