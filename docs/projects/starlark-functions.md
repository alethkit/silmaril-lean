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
before expansion. The supported `*` sources are lists, tuples, dictionary
keys and checked ranges. The supported `**` source is a dictionary with string keys. Expansion
preserves dictionary insertion order. When both expansions are invalid the
Go profile checks `**` first, after both operand expressions have run. A
call checks re-entry before binding parameters.

The pinned Bazel prose illustrates positional spreading with lists and
describes ranges as iterable, leaving range spreading unspecified.
Pinned Go calls `Iterate` on the `*` value and appends each yielded element,
so the Go-compatible profile accepts ranges, including slices. The shared
cursor collects the range in yield order after explicit positional arguments.
This materializes the argument sequence in host memory with exact integers
and leaves the language heap and iterator stack alone. Closure activation and
argument packs still use the existing allocation rules after successful
binding.
[Pinned functions][functions] · [Pinned ranges][range] · [Go operand ordering][go-call-compile] · [Go expansion and dispatch][go-call-expand]

The independent `ExpandsStar` range rule uses `CursorCollects`.
`expandsStar_iff_expandStar` proves exact agreement on yields or errors and
state. The rule composes with `evaluates_iff_denoteExpr` and `lower_preserves`
through the existing resolved call profile. The existing quotation and
resolver already admit a range-producing operand after `*`. Fixtures cover
mixed arguments, empty, descending and sliced ranges, operand effects, and
mapping validation before binding.
[Expansion theorem](../../Silmaril/Languages/Starlark/Functions/Expressions/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/functions/check.go)

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
it returns. A successful operand supplies the value for iterator acquisition.
An operand failure propagates its effects with
no loop target write or new guard.

`Body.forInExpr`, the call-free `Body.forIn`, and collection suites share
the same cursor and cleanup semantics for list, tuple, dictionary and
range operands. Each iteration assigns its target before running
the body. A callee shares heap identities and active
iterators with its caller, so the guard covers mutations through aliases.
The loop restores the guard stack left by operand evaluation on every
exit, including return and error.

`range` yields its current exact integer and advances by the descriptor's
stride. The remaining count bounds the cursor recursion. This works for
descending and sliced ranges and needs no enumerated sequence, heap guard
or execution fuel. The Lean fixtures break and return after the first
element of a range of length `10^24`. The pinned Go cursor advances an
offset and uses host `int` arithmetic. The common-profile fixtures exit
early from a billion-element range and check empty and sliced ranges,
operand effects, and cleanup after a nested failure.
[Pinned for statements][for-stmts] · [Pinned range spec][range] · [Go range iterator][go-range-iterator] · [Pinned Go fixtures](../../examples/starlark/call-loops/check.go)

`runChecked` validates calls in the operand and checks break and continue
in each declaration's own lexical loop context, including unreachable
code. `exec_iff_denoteBody` covers the exact result or error, frame, heap
and iterator stack. The available declaration set bounds live calls.
[Native loop agreement and cleanup](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Native loop fixtures](../../Silmaril/Languages/Starlark/Functions/NativeLoopChecks.lean) · [Collection loops](starlark-lists.md#iteration-and-control)

### Loop target patterns

A resolved `LoopTarget` is a name or a nested tuple/list pattern with name
leaves. Single-name calls can pass a `Binding`, and `LoopTarget.unpack`
builds the flat form from a list of bindings. At each sequence node the binder
checks the corresponding item's arity, then assigns its children in order.
Repeated names take their last assigned value. An empty pattern requires an
empty item. For `(a, [b, c], d)`, an outer arity mismatch writes nothing.
If the outer count matches and `[b, c]` fails, the new `a` survives, while
`b`, `c` and `d` keep their previous bindings. The loop skips its body and
later items and restores the operand's iterator stack.
[Pinned assignments][assignments] · [Pinned for statements][for-stmts] · [Go loop compilation][go-for-compile] · [Go target writes][go-unpack-compile] · [Go unpack checks][go-unpack]

The pinned prose describes sequence inputs, including ranges. The
Go-compatible profile also admits dictionaries, which yield their
insertion-ordered keys. Go emits `UNPACK` at each sequence node. It probes
for an extra item and closes the temporary iterator before assigning that
node's children. The Lean binder gets the same elements from the cursor. It checks
the count before collection, which makes a huge mismatched range reject
without enumerating it. The supported item cursors have no callback or
mutation during unpacking.
[Go iterator cleanup][go-loop-cleanup] · [Pinned Go fixtures](../../examples/starlark/call-loops/check.go)

`bindsTarget_iff_bindTarget` proves exact agreement with the independent
unpacking and write-order rules, including the state at a nested error.
`unpackValue_failure_state` preserves the incoming state of a failed node
check, and `bindsTarget_failure_state` gives the full failure guarantee
for flat targets. The binder composes with `exec_iff_denoteBody` and
`runs_iff_denoteSuite`. `lowerForIn_preserves` transports the binder's heap,
slots and visible writes through scratch projection before it uses the
existing body premise. Standalone pattern assignments and list and dictionary
comprehension assignments also use this binder. Subscript and field
leaves remain open.
[Binder and cursor theorems](../../Silmaril/Languages/Starlark/Lists/Iteration/Thms.lean) · [Lowering theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean) · [Source loop validation](starlark-modules.md#resolving-module-declarations)

## List comprehension assignment

The normalized function and module ASTs admit assigning a list
comprehension to a name. The first generator is required. Later clauses
can be generators or filters, followed by the element expression.
Each generator accepts a single name or a nested tuple/list pattern with
lexical name leaves. A comprehension introduces a lexical block containing
all generator names. Its first iterable evaluates once in the enclosing
block. All later operands, filters and elements use the new block,
including forward references that may fail as uninitialized. Duplicate
names in a pattern reuse a slot and are written left to right.
[Pinned comprehensions][comprehensions] · [Pinned name binding][names] · [Go resolution][go-comp-resolve]

The empty result list is allocated before the outer iterable, as in the
pinned Go compiler. The resolved core uses a scoped assignment, the
existing cursor, the independent target binder and the ordinary branch
and append actions. A mismatch keeps earlier sibling writes in the exact
heap, skips later children and the remaining clauses, and releases each
active iterator guard. Both exits restore the surrounding frame. The
destination receives the list only on success. At module scope the
ordinary publication path freezes the reachable result.
[Go clause compilation][go-comp-compile] · [Go guard cleanup][go-loop-cleanup] · [Resolved definitions](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Defs.lean)

`Comprehensions.exec_iff_denote` composes the independent scoped body,
loop and binder rules with their exact denotation. `Comprehensions.lower_preserves`
covers the first iterable, later iterable operands, filters and element
expressions. It assumes the existing expression admission and scratch
slot conditions. Each lowered operand discards its scratch writes while
retaining the heap and errors, so the entire outcome agrees exactly,
including the restored bindings and iterator stack. Call termination
still uses the finite declaration guard and cursor descent uses the
remaining element count. The proof starts at resolved syntax. The
source correspondence shares the elaborator.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Thms.lean) · [Normalized source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/ComprehensionChecks.lean)

Within a single evaluation, later iterations can read earlier writes to
the comprehension block. The Lean profile starts fresh on each visit to
the comprehension site. The pinned Go compiler places the locals in
the enclosing activation and retains their previous contents across
visits. For example, `[y for x in source if x or y for y in [2]]` yields
`[2]` on both runtimes when `source = [1]`. When the same site next runs
with `source = [0]`, Go again yields `[2]` and Lean reports uninitialized
`y`. The Go failure fixture observes mutations to shared values and
guard release through `Program.Init`. Lean also inspects the retained
comprehension slots in its residual heap.
[Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

## Dictionary comprehension assignment

Function and module dictionaries use the same scoped generators, name
patterns, filters and fresh-local policy as list comprehensions. A fresh
dictionary is allocated before the outer iterable. At each accepted
combination of bindings, the key expression runs once, then the value runs
once, then the ordinary dictionary write checks hashability and inserts the
pair. A key expression error skips the value. A value expression error takes
precedence over an unhashable key. Failure keeps prior operand effects and
the accepted dictionary prefix in the heap, releases active iterator guards
and leaves the destination untouched.
[Pinned comprehensions][comprehensions] · [Pinned dictionaries][dictionaries] · [Go key/value emission][go-comp-compile]

A repeated key replaces only its value, retaining the original key object
and its insertion position. This path uses indexed dictionary assignment.
Dictionary displays keep their duplicate-key rejection. The Go reference
emits `SETDICT` after both operands for comprehensions, and its table
updates an existing entry in place. Both runtimes use their existing
hashability rules for the supported key domain.
[Go insertion dispatch][go-dict-run] · [Go insertion order][go-comp-put] · [Lean insertion theorem](../../Silmaril/Languages/Starlark/Lists/Thms.lean)

`Comprehensions.dict_exec_iff_denote` gives exact native correspondence
through the independent scoped, loop, binder, expression and indexed
assignment rules. `Comprehensions.dict_lower_preserves` covers every
operand including the key and value. It uses the same admission and
scratch slot conditions as the list theorem and compares the exact outcome
and final state after restoring scratch. The source theorem shares the
elaborator. Successful module initialization freezes the reachable result.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/DictComprehensionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

## Comprehensions in checked expression positions

The normalized `CompExpr` grammar admits list and dictionary
comprehensions in return values, assignment RHSs for names and nested
name patterns, and parameter defaults. Its recursive nodes include calls,
conditional tests and arms, and both
operands of `and` and `or`. A call's callee, positional operands, named
operands, and optional `*` and `**` operands all admit the placement
grammar. Ordinary leaves retain the existing resolved expression grammar.
[Pinned comprehensions][comprehensions] · [Pinned conditionals][conditional] · [Pinned logical operators][logical-ops]

The placement compiler emits a checked body at the point the value is
needed. A call evaluates its callee once, then stages positional operands,
named operands, at most one `*` and at most one final `**` in source order.
After every stage succeeds, the shared call operation expands the saved
values, checks callability and binds arguments. The Go profile checks the
mapping before the iterable. Both expansion checks precede binding errors
such as a duplicate key from an explicit keyword and `**`. A repeated
explicit keyword is rejected statically, including in a skipped arm. A
later operand can mutate an earlier saved iterable before expansion, and
a failing operand skips expansion and dispatch.
[Pinned functions][functions] · [Go operand compilation][go-call-compile] · [Go expansion][go-call-expand] · [Go binding][go-parameter-binding]

Conditions execute one arm, and a short circuit returns the saved left
operand with its effects. The scoped expression bodies restore private
bindings on exit. They reuse the comprehension accumulator, nested name
binder, fresh locals and iterator cleanup. Failure preserves earlier
effects and leaves the destination untouched. Call termination retains
the finite declaration guard.

The correspondence uses the independent checked body rules over the
emitted direct code. `Expression.lower_preserves` compares the exact
outcome, frame, heap and guards with scratch lowering.
`Expression.exec_iff_lowered` and `Expression.exec_return_iff_lowered`
connect these results to the independent assignment and return derivations.
Separate equations state the call order, conditional selection, short
circuiting, callee failure and argument sequencing. The proofs start
with resolved expression placement and use the existing admission and
scratch-slot assumptions. The normalized source correspondence shares its
elaborator.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

The same grammar admits comprehensions within list and tuple elements,
dictionary display keys and values, and the receiver and index of a
single subscript read. Lists and tuples evaluate elements left to right
and allocate only after every element succeeds. Dictionary displays
allocate an empty accumulator first. Each key and value run in order,
then the display insertion checks hashability and duplicates before the
next pair. A failed value takes precedence over an unhashable key.
[Pinned lists][list-expr] · [Pinned dictionary displays][dict-expr] · [Go list compilation][go-comp-display] · [Go dictionary compilation][go-dict-compile]

Dictionary displays retain the distinct duplicate rejection policy.
Lean keeps the accepted prefix in its private accumulator. Go's
`SETDICTUNIQ` updates the duplicate entry before reporting the error.
The failed display never publishes this private dictionary in either
runtime. The differential fixtures compare visible effects and errors,
while Lean tests the exact private heap as well.
[Go duplicate handling][go-dict-run]

Subscript reads evaluate the receiver and then the index. Validation
uses the existing read primitive after both operands succeed. A failed
receiver skips the index, and an index expression error precedes
validation of a successfully evaluated receiver. The body scopes retain
earlier effects, restore the caller's bindings and iterator guards, and
leave the destination untouched when an operand or final operation fails.
`display_entry_order` and `index_order` state these staging boundaries.
The exact assignment and return correspondence covers the new cases
with the same admission assumptions.
[Pinned subscripts][subscript] · [Go index compilation][go-index-compile] · [Go validation][go-index] · [Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean)

Slice placements accept the receiver and all present start, stop and
stride expressions. The normalized source records missing bounds as
`none`. Resolution fills those positions with pure Starlark `None`
operands. Present operands run once in receiver, start, stop and stride
order. Validation then checks the receiver kind, checks the stride and
rejects zero, and checks start before stop. A failure in any operand
takes precedence over that validation and skips all remaining operands.
The existing slice operation supplies the defaults, including the
distinction between an omitted stop and an explicit `-1` with a negative
stride.
[Pinned slices][slice-expr] · [Go operand compilation][go-slice-compile] · [Go slice validation][go-slice-eval]

`slice_order` states the four staging steps and the final shared read.
The assignment and return correspondence covers the exact caller
bindings, heap and iterator guards for direct and scratch-lowered
execution. The Go fixtures compare returned values, effects, errors and
guard release. Lean also checks private heap allocations and restored
bindings, which the Go fixture cannot observe. The existing slice value
and integer profiles still govern the final operation.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

In both list and dictionary comprehensions, each iterable and filter
can contain a comprehension. Resolution uses the enclosing lexical
environment for the first iterable. Every name introduced by a
generator belongs to the new block for later iterables, filters and the
head, including forward reads that can be uninitialized. A nested
comprehension's first iterable resolves in its own enclosing
environment, which may be the surrounding comprehension block.
[Pinned lexical scope][names] · [Go resolution][go-comp-resolve]

Evaluation allocates the accumulator and evaluates the first iterable
before allocating target slots or acquiring the first cursor.
A later iterable or filter runs only when reached by the surrounding
cursor and filters. A false filter skips the remaining clauses on that
iteration. A failing operand keeps earlier effects and skips the
remaining clauses. The existing cursor machinery unwinds guards on
both exits. If a nested operand iterates an alias already guarded by
the enclosing comprehension, completing the nested iterator leaves the
outer guard active.
[Go clause compilation][go-comp-compile] · [Go iterator cleanup][go-loop-cleanup]

The exact assignment and return theorems now cover nested clause
operands, including the residual heap and guard stack on failure.
`first_iterable_failure` states the failure boundary before the first
cursor and target scope. The source theorem shares the resolver.
The differential fixtures cover capture and shadowing, forward
uninitialized reads, short circuiting, same-alias guard lifetimes and
nested unwind. Lean still starts with fresh locals for each evaluation.
Go can keep their prior values across visits in one activation.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

A list comprehension's head element and a dictionary comprehension's
head key and value also accept the placement grammar. The head runs only
when all clauses have accepted a combination of bindings. Nested heads
resolve in that comprehension block and install their own locals.
Dictionary heads evaluate the key and then the value, and only then
check the key and insert or overwrite the entry in its original position.
A value error therefore takes precedence over an unhashable key, and a
failed key skips the value. These updates use the shared comprehension
accumulator path. Dictionary displays keep their duplicate-key rejection.
[Go head compilation][go-comp-compile] · [Go update dispatch][go-dict-run]

`dict_yield_order` gives the key, value and update sequence.
The exact assignment and return correspondences cover nested heads.
Comprehension locals are restored and the prior iterator stack is
preserved on success and failure. A failing head leaves earlier effects
and accumulator entries in the Lean heap and leaves the assignment
destination untouched. The pinned
Go fixtures compare effects and errors and check that guarded aliases
can be mutated after failure. Lean additionally compares the private
accumulator and frame. The fresh-local difference with Go also applies
when a nested head site is revisited within one outer comprehension.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

The normalized `CompExpr.listComprehension` and
`CompExpr.dictComprehension` forms accept recursive operands in clauses
and heads. The plain-head forms remain available. Quotation supplies
ordinary leaves and pattern ASTs. The recursive comprehension nodes
are constructed separately. Subscript stores, field targets, and other
statement operands remain outside this placement boundary.
Call shapes and spread value domains follow the
[existing argument profile](#argument-binding).

### Comprehensions in parameter defaults

A positional or keyword-only default may use the same normalized
placement grammar in a module or nested function definition. The resolver
reads defaults in the defining scope before entering the parameter and
body scope. Reads from further enclosing functions contribute to the
defining closure's captures.
[Pinned functions][functions] · [Pinned definitions][defs] · [Go default resolution][go-default-resolve]

For definitions that use this grammar, the emitted body evaluates the
optional operands once, in positional then keyword-only declaration
order. It stages their values in private bindings. The existing
closure installer reads the saved values after all operands succeed.
The outer scope drops the staging bindings on either exit. The
definition writes the function name only on success. A failing operand
skips later defaults, keeps earlier heap effects and unwinds its
iterator guards. Omitted arguments use the closure's saved values,
including the original mutable objects. Module publication freezes
the values reachable through those defaults.
[Go evaluation order][go-default-compile] · [Go definition assignment][go-define] · [Go default reuse][go-default-bind]

`definition_defaults_preserved` and `definition_exec_iff_lowered` compare
the complete staged definition in the existing finite declaration
context. Their hypotheses are operand admission and a scratch-free
input. They cover the exact outcome, frame, heap and iterator stack.
The source correspondence shares normalized elaboration. Quotation
still supplies only ordinary operands and target patterns.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

Lean continues to start each comprehension evaluation with fresh
locals. A default of
`[[y for x in source if x or y for y in [2]] for source in [[1], [0]]]`
fails with uninitialized `y` in Lean and produces `[[2], [2]]` in Go.
The Go error fixture observes reachable effects and released guards.
The Lean fixture also compares private staging cleanup and preservation
of a previous function binding.
[Pinned name binding][names] · [Go comprehension compilation][go-comp-compile]

## Direct denotation of resolved expressions

`Lowering.denoteExpr` maps a resolved expression and state to a value or
dynamic error with its final state. It interprets call-free collection
atoms, list, tuple and dictionary displays, subscript and slice reads, nested calls with positional,
keyword, `*` and `**` operands, conditionals and operand-valued `and` and
`or`. A call evaluates the callee and operands from left to right, then
expands and binds the arguments.
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

### Collection displays and subscript reads

`Expr.list` and `Expr.tuple` evaluate elements once from left to right and
allocate after all elements succeed. Tuple allocation uses the existing
structural key cache. `Expr.index` evaluates its receiver once,
then its subscript once, and reads from the resulting heap. A receiver
error skips the subscript. An operand or lookup error retains the effects
preceding it. The independent rules and denotation share the existing
allocation and lookup primitives. The expression and body agreement
theorems include the exact result or error and residual state.

`Expr.dict` allocates an empty dictionary before evaluating the first pair.
It evaluates the key, then the value, then checks and inserts the pair before
the next key. A value error takes precedence over hash or duplicate checking
for that pair. Failure preserves prior effects and the dictionary's accepted
prefix. The older call-free `Lists.Code.dict` still allocates after collecting
the pairs. The two forms have distinct internal heap allocation schedules.

The pinned Go bytecode uses the same key/value and insertion order. Its
duplicate-error instruction replaces the old value in its private dictionary
before raising the error. The Lean heap retains the original accepted prefix.
The Go fixture compares ordinary values, errors and effects visible to callers.
The prose spec allows a frozen-container exception to unhashability. The
shared Lean key policy and pinned Go reject list and dictionary keys even
after freezing.
[Dictionary expressions in the pinned spec][dict-expr] · [Hashing in the pinned spec][hashing] · [Go compiler][go-dict-compile] · [Go interpreter][go-dict-run]

Subscript reads accept lists, tuples, dictionaries, strings and ranges. Sequence
reads use exact integers and allow negative indices. Go supports
additional indexable types and checks sequence indices through a signed
32-bit conversion. Byte indexing remains open.
[List expressions in the pinned spec][list-expr] · [Tuples in the pinned spec][tuple-expr] · [Subscripts in the pinned spec][subscript] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

### String subscript reads

The receiver and index evaluate once in that order. A receiver evaluation
error skips the index, and an index evaluation error takes precedence over
receiver and index validation. Both operand effects survive a validation
error. The receiver kind determines whether to apply integer indexing.
For strings, the evaluator checks the index type and bounds against the UTF-8
byte length before selecting the byte. Negative indices offset from that
byte length. A successful read returns a one-byte string, with no heap
allocation.

The pinned spec allows an implementation to disallow operations that
produce invalid Unicode. In this valid UTF-8 profile, selecting an isolated
lead or continuation byte raises `invalidIndexUTF8`. Pinned Go preserves
that byte in a string. For example, `"éz"[0]` produces raw byte `c3` in Go
and errors in Lean, while `"éz"[-1]` yields `"z"` in both.

The existing subscript rule and direct denotation share this primitive.
`evaluates_iff_denoteExpr` covers exact outcomes and residual state.
`lower_preserves` covers the emitted index expression after scratch
projection, including keeping the destination binding on failure. The
normalized source and Lean quotation use the existing `receiver[index]` form.
[Pinned strings][strings] · [Pinned subscripts][subscript] · [Go operand compilation][go-index-compile] · [Go validation][go-index] · [Go byte indexing][go-string-slice] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

### Lazy range subscript reads

`range` accepts one to three positional integers and rejects a zero step.
The result stores the start, exclusive stop and nonzero step. Its length
comes from the distance to the stop and the step magnitude. Direction
mismatches give an empty range. Construction and subscripting use a fixed
number of integer operations and allocate no Starlark heap cells.

The receiver and index evaluate once, from left to right. A failed range
constructor stops evaluation before the index. Once the receiver and index
succeed, the same sequence normalization used for lists and tuples checks
the index type and bounds. Negative indices count from the range length.
The selected value is `start + offset * step`. Indexing leaves all earlier
effects intact on either outcome.

Lean uses exact integers for range parameters, lengths, indices and results.
Pinned Go converts constructor arguments to host `int`, computes the length
in that type, and converts the index to signed 32 bits before sequence
bounds. On amd64, the Go fixture distinguishes constructor overflow, an
in-range index above `2^31 - 1`, and wraparound of the length calculation
even when both endpoints fit. The Lean fixture succeeds on those exact
integer cases.

The new built-in rules and subscript primitive compose with
`evaluates_iff_denoteExpr` and `lower_preserves` for exact outcomes and
state after scratch projection. Normalized source and Lean quotation use
ordinary calls and subscripts. Range truth, length and type are available.
The `list` and `tuple` built-ins materialize ranges through the same cursor
as loops, and `*` materializes their elements as positional arguments.
Range comparison, membership and formatting remain open.
[Range materialization](starlark-builtins.md#materializing-ranges) · [Argument binding](#argument-binding)
[Pinned range spec][range] · [Pinned subscripts][subscript] · [Go range construction and indexing][go-range] · [Go index validation][go-index] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

### List and tuple slice reads

`Expr.slice` evaluates the receiver, start, stop and stride once, from left
to right. The first operand evaluation failure skips the rest and retains
its effects. After all four succeed, the evaluator reads the receiver in the
resulting heap, then validates the stride, start and stop in that order.
An unsupported receiver takes precedence over invalid bound values. A zero
stride takes precedence over start and stop type errors. This validation
order follows pinned Go.

Omitted bounds elaborate to `None` and explicit `None` has the same runtime
meaning. The default stride is 1. Negative bounds offset by the current
length. The signed stride determines the defaults and clamp interval.
The stop is exclusive in either direction, so an omitted stop in a reverse
slice differs from an explicit `-1`. Lean uses exact integers, including
bounds and strides beyond Go's signed 32-bit conversion.

A successful slice allocates a fresh outer collection of the receiver's
kind, even when the result is empty. Element values are copied shallowly,
so mutable elements retain their identities. A list result starts mutable.
Tuple allocation recomputes the structural key from the selected elements.
The heap model allocates a tuple cell even for unit stride, where Go can
reuse part of the backing array of the immutable tuple.

The operational rule uses ordered operand derivations and shares the
value-level selection and allocation primitive with the denotation.
`evaluates_iff_denoteExpr` compares the exact outcome and state.
`lower_preserves` covers slice reads after projecting direct scratch bindings.
The normalized resolver and Lean quotation admit `xs[a:b:s]` with optional
bounds. Slice reads on bytes remain open.
[Pinned slice spec][slice-expr] · [Go compilation][go-slice-compile] · [Go validation][go-slice-eval] · [Go list slice][go-list-slice] · [Go tuple slice][go-tuple-slice] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

### String slice reads

String slices use the same operand and validation order, exact integer
normalization, and slice selection as lists and tuples. The input elements
are UTF-8 bytes, consistent with the existing `len`. The evaluator decodes
the selected bytes only after slicing, including when the stride is
negative. A valid result is an immutable string value and allocates no
heap cell. An invalid result raises `invalidSliceUTF8` and retains all
operand effects. Both outcomes are covered by `evaluates_iff_denoteExpr`
and `lower_preserves`. The existing resolver and quotation accept string
receivers through the same expression form.

This is the pinned spec's 8-bit profile that disallows invalid Unicode
encodings. Pinned Go accepts the malformed bytes from a split sequence or
byte reversal as a string. For example, `"é"[:1]` yields the byte `c3` in
Go and raises `invalidSliceUTF8` in Lean. `"aé🙂z"[1:-1]` yields
`"é🙂"` in both. The distinct `bytes` value type remains open.
[Pinned strings][strings] · [Pinned slice spec][slice-expr] · [Go string indexing and slicing][go-string-slice] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

### Lazy range slice reads

Range slices use the same operand order and checked offset normalization
as list, tuple and string slices. The normalized offsets form a range in
index space. The result maps the normalized start and exclusive stop
through the receiver's affine map and multiplies the two strides. Its
stride stays nonzero. `RangeValue.slice_atOffset` proves that the resulting
map applies the normalized offset map before the receiver's map. Nested
slices repeat the same composition. Range slicing calculates a new
descriptor without enumerating elements or allocating a Starlark heap cell.

An empty result stays empty under further slicing. Lean retains independently
clamped bounds for a slice with crossed endpoints. Go collapses crossed
bounds to equal endpoints, which gives the same empty length and index
errors. Descriptor formatting remains outside this profile.

Pinned Go converts explicit start, stop and stride operands to signed
32 bits and composes ranges with host `int` arithmetic. On amd64 the
fixtures show two nonempty slices becoming empty in Go after wraparound,
one in the composed stride and one in the mapped stop. Lean computes all
these values exactly.

The existing independent slice rule and direct evaluator share the
value-level primitive. `evaluates_iff_denoteExpr` and `lower_preserves`
cover exact outcomes and residual states, including earlier effects
and an unchanged destination on failure. The normalized resolver and
Lean quotation use ordinary slice syntax, including nested slices.
[Pinned range spec][range] · [Pinned slice spec][slice-expr] · [Go validation][go-slice-eval] · [Go range composition][go-range-slice] · [Point correspondence](../../Silmaril/Languages/Starlark/Lists/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Expressions/CollectionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/nested-expressions/check.go)

## Native expression positions

`Body.returnExpr`, `Body.assignExpr`, `Body.evalExpr`, `Body.branchExpr` and `Body.forInExpr`
evaluate a resolved expression in the current frame. A successful return operand produces the
return signal. Assignment writes its destination with the existing binding
semantics after the right-hand side succeeds. An expression statement discards
its successful result and keeps the resulting state. A successful test is converted
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

Module commands reuse native assignment and expression statements, including
direct collection displays, subscript and slice reads, and the assignment forms below.
[Body rules](../../Silmaril/Languages/Starlark/Functions/Operational/Defs.lean) · [Native position agreement](../../Silmaril/Languages/Starlark/Functions/Lowering/Denotation/Thms.lean) · [Assignment and conditional fixtures](../../Silmaril/Languages/Starlark/Functions/NativeBodyChecks.lean) · [Return fixtures](../../Silmaril/Languages/Starlark/Functions/NativeReturnChecks.lean) · [Coverage obligations](starlark.md#coverage-obligations)

### Standalone pattern assignment

`Body.assignTargetExpr` evaluates the RHS once in the current frame, before
any target write. It then uses the nested tuple/list binder. A failed RHS
retains its effects and skips binding. After a successful RHS, each node
checks its own item and arity before writing children left to right. A later
child failure keeps earlier sibling writes. The same rules apply to the
lexical name leaves in checked functions and the global leaves in checked
module commands. Repeated function names write the same slot in order.
Module validation rejects duplicate globals, including repeats in one
pattern, before execution.
[Pinned assignments][assignments] · [Pinned lexical rules][names] · [Go RHS before target][go-assignment] · [Go global binding][go-bind-global]

`exec_assignTargetExpr_iff_denoteExpr` composes independent RHS and binder
rules with the direct denotation. `lowerAssignTarget_preserves` proves that
staging the RHS in a scratch binding preserves success and both kinds of
failure, including the exact heap, slots, iterator stack, and visible
bindings. Checked module commands use the direct body evaluator and the
existing initialization and publication rules. This slice admits name
leaves under nested tuple/list patterns.
[Native and lowered fixtures](../../Silmaril/Languages/Starlark/Functions/NativeBodyChecks.lean) · [Source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/functions/check.go)

#### Comprehension right-hand sides

`assignTargetCompExpr` accepts a normalized `CompExpr` RHS and the same
name-leaf pattern in function and module code. After the scoped RHS
returns, the evaluator restores the enclosing frame and runs the
existing binder on the saved value. The heap and iterator state come
from RHS execution. Restoring the frame before binding keeps any
earlier target writes when a later nested arity check fails, including
direct binding writes in a resolved state without allocated target slots.
On RHS failure the binder does not run.
[Pinned assignments][assignments] · [Go RHS order][go-assignment] · [Go recursive pattern order][go-unpack-compile] · [Go unpack checks][go-unpack]

`Expression.exec_assignTarget_iff_lowered` connects the independently
stated RHS-body and binder premises to exact scratch-lowered outcomes
for admitted RHSs from scratch-free states. It includes residual heap,
frame and iterator state on either kind of failure. The proof shares
normalized lexical resolution and inherits finite declaration descent.
The Go fixtures observe target writes, effect order and guard release.
The Lean fixtures also compare the private frame and heap. Comprehension
revisits retain the [fresh-local profile](#comprehensions-in-parameter-defaults).
Quotation, comprehension RHSs in subscript stores, subscript and field
pattern leaves, and augmented pattern assignment remain separate.
[Theorems](../../Silmaril/Languages/Starlark/Functions/Comprehensions/Expression/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/CompExpressionChecks.lean) · [Pinned Go fixtures](../../examples/starlark/comprehensions/check.go)

### Simple subscript assignment

`Body.setIndexExpr` evaluates the RHS, then the receiver, then the subscript,
once each. It applies `Lists.writeIndex` to the heap produced by those three
operands. An operand error retains its state and skips all later work. The
independent rules and direct denotation agree on the exact `next` or error
outcome and residual frame, heap and iterator stack. Closure calls use the
same finite declaration descent as other native expression positions.

The list write checks index type and bounds against the current length before
the freeze or iterator guard. A dictionary write checks those guards before
hashing the key. These competing-error orders match pinned Go. The Lean list
index is an exact integer. Go converts it to signed 32 bits before the bounds
check. Successful writes are visible through aliases. Dictionary replacement
keeps the entry's position, and a new key goes at the end.

Normalized function and module statements expose `setIndex receiver subscript rhs`.
The three expressions can use the existing quotation. A subscript assignment
creates no lexical binding. Slice and compound targets and user-defined item
assignment remain open.
[Assignments in the pinned spec][assignments] · [Go assignment compilation][go-assign] · [Go write dispatch][go-write] · [Go dictionary checks][go-dict-write] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/NativeSubscriptChecks.lean) · [Pinned Go fixtures](../../examples/starlark/subscript-assignment/check.go)

### Integer augmented subscript assignment

`Body.addIndexExpr` evaluates the receiver and subscript once, in that
order, and reads the old value before evaluating the RHS. It then adds the
old value and the RHS result as exact integers and writes the sum. The
first failure stops execution with its residual state. A failed read
skips the RHS. A failed addition precedes any write guard. A frozen or
active iterator error comes from the final write after the RHS effects.

Write-back uses the saved receiver identity and raw subscript in the heap
left by the RHS. For a negative list index, the read and write each
normalize against the length at that step. If the RHS grows the list,
write-back can replace a different element of the same list. The pinned
spec requires target subexpressions to run once before the RHS. Pinned Go
also confirms the read and write timing and negative-index behavior.

`exec_addIndexExpr_iff_denoteExpr` compares the independent operational
rules with the direct denotation on the exact outcome, frame, heap and
iterator stack under the existing finite declaration descent. Normalized
function and module statements expose `addIndex receiver subscript rhs`
without introducing a lexical binding. Successful writes cover existing
list elements and dictionary entries. Operand pairs outside integer addition
report `integerAddType` in this profile. Other augmented operators, name
and field targets, and Go's in-place list addition remain open.
[Augmented assignments in the pinned spec][augmented] · [Go compilation][go-augmented] · [Go operator dispatch][go-inplace-add] · [Go write dispatch][go-write] · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/NativeSubscriptChecks.lean) · [Pinned Go fixtures](../../examples/starlark/subscript-assignment/check.go)

## Nested expression lowering

`Lowering.lower` compiles resolved expressions to a `Body` and a list of
scratch slots. It stages the callee and every call operand,
including call-free operands, before the final call. Positional, keyword,
`*` and `**` operands stay in source order. Expansion and argument errors
still use the call semantics. The compiler places branch work inside the
selected branch and skips its destination write if the operand fails. List
and tuple displays, subscript reads and slice reads stage their operands before the final
collection operation. Dictionary lowering stages a key and value, checks and
inserts the pair into the dictionary, then continues with the next pair.

Use the frame's direct bindings for scratch names when comparing exact
heaps. In this mode, omit the compiler scratch names from the heap-backed
slot map. They use a prefix outside the source identifier grammar. Thread
the returned `next` value into further lowering in the same frame to keep
ranges disjoint. The emitted code can be placed inside a function loop.

`lower_preserves` relates an independent source evaluation to
`denoteBody` of the emitted code. The proved fragment includes call-free
atoms, list, tuple and dictionary displays, subscript and slice reads, nested calls with positional, keyword,
`*` and `**` operands, conditionals and short-circuit operations. The source rules evaluate the
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

`lowerForIn` stages the iterable in a scratch binding before the shared
loop reads it. `lowerForIn_preserves` relates native and staged loops on
every outcome after projecting scratch bindings. Given an independent
operand evaluation and a scratch-free entry state, the theorem requires
that the pair of supplied bodies preserve the same projection at each
related body entry. The cursor transports that premise through binder
writes, continuation and cleanup.
[Loop lowering theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean)

Native module assignments and expression statements use the direct denotation.
Static validation of repeated explicit keywords stays with the checked entry points.
Supported iterable, mapping and callable values are those of the
shared-store call profile above.
[Preservation theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean) · [Independent source rules](../../Silmaril/Languages/Starlark/Functions/Lowering/Source/Defs.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/PreservationChecks.lean) · [Go fixtures](../../examples/starlark/nested-expressions/check.go)

## Resolving a normalized expression

`Lowering.Resolve.resolve` takes an unresolved expression and a lexical
context collected by the caller. It accepts integer and string literals,
identifier reads, list, tuple and dictionary displays, single-expression subscripts, calls with all
four operand classes, conditionals and operand-valued `and` and `or`. It uses
the scalar resolver's precedence
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
slots. `resolveTracked` also returns the lexical slots read during resolution.
The [module adapter](starlark-modules.md#resolving-module-declarations)
collects scopes and uses those reads for closure captures. Text parsing,
source locations and attribute syntax
remain outside the expression adapter. The preservation theorem starts at
the resulting resolved tree.
[Resolver](../../Silmaril/Languages/Starlark/Functions/Lowering/Resolve/Defs.lean) · [End-to-end Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Lowering/Resolve/Checks.lean)

## Quoting an expression in Lean

`starlark%[...]` constructs a `Lowering.Resolve.SourceExpr` in a Lean file.
It accepts grouped expressions, simple ASCII identifiers, decimal integer
literals with optional minus, plain double-quoted strings, list and dictionary displays, parenthesized tuples,
single-expression subscripts, slices, nested calls, conditionals and operand-valued
`and` and `or`. Calls accept positional
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
binary `+`, duplicate explicit keywords and
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
  +Silmaril.Languages.Starlark.Functions.NativeSubscriptChecks \
  +Silmaril.Languages.Starlark.Functions.Expressions.CollectionChecks \
  +Silmaril.Languages.Starlark.Functions.LoopChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.PreservationChecks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Checks \
  +Silmaril.Languages.Starlark.Functions.Lowering.Quote.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.CompExpressionChecks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/functions/check.go" && go run "$fixtures/call-loops/check.go" \
  && go run "$fixtures/nested-expressions/check.go" && go run "$fixtures/subscript-assignment/check.go" \
  && go run "$fixtures/comprehensions/check.go")
```

Module initialization, prepublished imports and the checked universal built-ins
extend this profile. Host callable effects remain open.
[Modules](starlark-modules.md) · [Built-ins](starlark-builtins.md)


[functions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[defs]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions
[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[list-expr]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#list-expressions
[tuple-expr]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#parenthesized-expressions
[dict-expr]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionary-expressions
[hashing]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#hashing
[go-dict-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1371-L1380
[go-dict-run]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L469-L486
[subscript]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#subscript-expressions
[range]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#range
[for-stmts]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[assignments]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#assignments
[go-for-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1172-L1192
[go-unpack-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1247-L1293
[go-assignment]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1092-L1099
[go-bind-global]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L314-L347
[go-unpack]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L508-L533
[go-loop-cleanup]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L102-L113
[go-range-iterator]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L951-L964
[go-call-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1650-L1728
[go-call-expand]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L298-L382
[go-range]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L827-L879
[go-range-slice]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L881-L891
[go-index-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1334-L1338
[go-index]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L681-L717
[slice-expr]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#slice-expressions
[strings]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#strings
[go-slice-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1340-L1358
[go-slice-eval]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1266-L1381
[go-list-slice]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L992-L1004
[go-tuple-slice]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L1131-L1142
[go-string-slice]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go#L560-L597
[assignments]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#assignments
[augmented]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#augmented-assignments
[go-assign]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1247-L1272
[go-augmented]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1124-L1166
[go-inplace-add]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L217-L244
[go-write]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L719-L746
[go-dict-write]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L78-L88
[go-function]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/value.go

[comprehensions]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#comprehensions
[go-comp-resolve]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L686-L708
[go-comp-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1745-L1804
[dictionaries]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#dictionaries
[go-comp-put]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/hashtable.go#L78-L150
[conditional]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#conditional-expressions
[logical-ops]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#or-and-and
[go-parameter-binding]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1429-L1480
[go-default-resolve]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L819-L833
[go-default-compile]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1808-L1850
[go-define]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1169-L1171
[go-default-bind]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/eval.go#L1482-L1510
[go-comp-display]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/internal/compile/compile.go#L1310-L1314
