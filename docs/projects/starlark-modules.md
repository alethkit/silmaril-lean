# Starlark module publication and imports

The profile follows the Bazel-team core specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. Raw `spec.md` has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Module execution][modules] · [Load statements][loading]

`Silmaril.Languages.Starlark.Modules.Thms` exposes the resolved entry point
`initializeModule`. It checks argument-list legality and conflicting global
and file names before allocating slots. It executes top-level commands in
order. `TopCode.assignExpr` writes one global after evaluating a resolved RHS,
and `TopCode.evalExpr` evaluates a resolved expression and discards the value.
Both admit nested calls with keyword and spread operands, conditional
expressions, and short-circuit operators in the [direct expression profile][expressions].
Runtime errors retain operand effects without writing the assignment target
or running later commands. Existing atomic commands, definitions, calls,
and loads with named aliases use the same lifecycle. Temporary slots used
by call lowering and file-local imports remain outside the export list.

The entry point assumes resolved bindings, the list of declared globals,
single assignment of explicit globals, and legal load identifiers. The
[source adapter](#resolving-module-declarations) collects the scopes for an
admitted normalized AST.
[Definitions](../../Silmaril/Languages/Starlark/Modules/Defs.lean)

The host supplies a pure catalog of already published modules. It determines
how labels are interpreted. All modules in a catalog share the same heap
and the same linked function-declaration table. An imported value retains
its address, so calling an imported closure uses that closure's original
global slots. A missing catalog entry and a missing exported name are
distinct failures. Private import names are rejected during validation.
A single load resolves all its requested exports before binding their aliases.
[Load statements][loading] · [Lexical calls](starlark-functions.md)

A new module begins with fresh slots and no inherited active iterators.
Successful completion freezes all global values, including private ones,
before publishing the public export table. Runtime failure returns the
updated heap with the caller's scope and iterator context restored. The
failure path publishes no module and performs no publication freeze.
A caller supplies both the initial heap and any prepublished imports.
The heap may retain unreachable allocations.
[Module execution][modules] · [Reachable freezing](starlark-lists.md#reachable-freezing)

`runs_iff_runCommands` proves exact agreement before publication, including
the module and file namespace and the shared heap at the first failure.
`initializes_iff_initialize` extends agreement through the publication
boundary, comparing the export table or error and the entire residual
state after restoring the caller. Both proofs compose independent command
sequencing with `Exec`; its native expression rules derive calls and callee
bodies independently of the direct denotation. The module rules and
denotation share validation, namespace entry, the pure catalog contract,
and publication or failure restoration. Calls start with the finite linked
declaration table and remove the active declaration on descent.
[Operational rules](../../Silmaril/Languages/Starlark/Modules/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Modules/Thms.lean)

## Resolving module declarations

`Modules.Resolve.resolve` takes normalized source commands and returns a
checked `Modules.Source` and linked declaration table. Module commands cover
single-name and [nested name-pattern assignment][pattern-assignment], [simple subscript assignment][subscript-assignment],
[integer subscript `+=`][augmented-subscript], expression statements, `def` and
named `load` imports. Function bodies add nested `def`, sequencing, `if`, `pass` and
`return`, as well as `for` loops with `break` and `continue`.
Signatures represent the positional, keyword-only, `*args` and
`**kwargs` classes used by the existing binder. Operands use the
[existing source expression profile][source-expressions], including the Lean
expression quotation.

The resolver collects globals and load aliases across the file, and
parameters and assigned names across each function body. A lexical binding
shadows outer names throughout its block. Undefined names fail statically
even in skipped code. A forward reference resolves to the slot but fails
dynamically if read before its assignment or load. Duplicate module bindings
and load/global collisions are rejected before execution.

For standalone destructuring, `Statement.assignTarget` resolves each name
leaf to a function slot and `Command.assignTarget` resolves each leaf to a
module global. The resolver collects those names before analyzing any RHS.
Both contexts also accept `assignTargetCompExpr` with the same target and
a `CompExpr` right-hand side. This form also accepts subscript leaves
whose receiver and index use the ordinary resolved expression grammar.
Only identifier leaves join the enclosing lexical block.
The module command uses the shared direct binder in source order. A failed
initialization retains earlier heap effects, including partial writes into
its slots, and follows the existing failure path without publication.
[Pattern semantics][pattern-assignment] · [Source assignment fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

The `assignListComp` and `assignDictComp` forms in `Statement` and
`Command` resolve comprehensions assigned to a name. Only that destination joins the
enclosing block. The first iterable uses the enclosing scope and the
remaining clauses resolve with all generator names local to the
comprehension. Quoted expressions can supply the pattern, iterable,
filter and yield ASTs, including dictionary key/value pairs. Resolved module
commands enter the same body
path as function assignments, then use the ordinary publication rules.
[List comprehension semantics](starlark-functions.md#list-comprehension-assignment) · [Dictionary comprehension semantics](starlark-functions.md#dictionary-comprehension-assignment)

The normalized `CompExpr` adapter allows comprehensions in call operands,
conditional and short-circuit operands, collection displays, and index
and slice reads within return values, assignment RHSs for names and
nested name patterns, operands of standalone simple and integer
augmented subscript stores, function-local integer augmentation, and
parameter defaults.
The first and later iterables and filters and the heads of a comprehension
use the same broader placement grammar.
Both selected and skipped AST positions are resolved before execution.
The emitted body evaluates only reached operands, preserves their order
and keeps prior shared heap effects on failure.
[Expression placement](starlark-functions.md#comprehensions-in-checked-expression-positions)

A loop target belongs to the whole function block. The resolver collects
all target names before resolving the iterable and body in that block. Thus
`for x in x` reads the function's `x` before any iteration writes it. The
last assignment to the target is visible after the loop, and an empty
loop performs no target write. Loops emit `Body.forInExpr` and use
the existing validation of `break` and `continue` in each function, including
skipped code and nested definitions. Tuple and list patterns with lexical
name leaves enter through `Statement.forInTarget`, for example
`.forInTarget starlark%[(x, [y, z])] starlark%[rows] .pass`. The resolver
rejects non-name leaves even in skipped code. A single identifier can use
`Statement.forIn`. The module command type admits
only top-level forms permitted in this profile.
[For statements in the pinned spec][loops] · [Resolved loops](starlark-functions.md#calls-inside-loops) · [Source loop fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/LoopChecks.lean)

Defaults resolve in the enclosing scope. Function bodies use the function's
own parameters and locals, and each declaration captures the free slots its
body or nested definitions need. A definition passes those slots through any
intervening function. The evaluator runs defaults when it executes the
definition command and installs the closure only after they succeed.
`SourceParameter.defaultExpr` accepts the normalized `CompExpr` grammar.
An ordinary quoted `SourceExpr` coerces to a plain expression.
[Name binding in the pinned spec][names] · [Resolver](../../Silmaril/Languages/Starlark/Modules/Resolve/Defs.lean) · [Comprehension defaults](starlark-functions.md#comprehensions-in-parameter-defaults)

```lean
module

import Silmaril.Languages.Starlark.Modules.Resolve.Defs
import Silmaril.Languages.Starlark.Functions.Lowering.Quote.Defs

open Silmaril.Languages.Starlark.Modules.Resolve
open scoped Silmaril.Languages.Starlark.Functions.Lowering.Quote

def exampleModule : List Command := [
  .assign "seed" starlark%["definition scope"],
  .define "pick" { positional := [⟨"seed", some starlark%[seed]⟩] }
    (.ret (some starlark%[seed])),
  .assign "out" starlark%[pick()]]

def exampleResult := runModule exampleModule (fun _ => none) {}
```

This module exports `out = "definition scope"`. `runModule` reports
elaboration errors separately from runtime errors and uses the resolved
module initialization and publication rules. Supply the existing linked
table when catalog values can contain closures. Resolving another module
appends declarations and preserves the IDs already in that table. To use
the finite loader, clients assemble the manifest and link its resolved
sources to one table.

`checked_of_resolve` states exactly which checked source and declaration
table successful elaboration produces, including the globals in source order
and absence of compiler scratch slots. `initializes_iff_runModule` composes
the elaboration result with the resolved operational theorem. It compares
static rejection, execution outcomes, publication and the exact residual
state. This correspondence shares the elaborator and starts at a normalized
AST with legal identifier spellings. A separate
[mixed assignment theorem](starlark-functions.md#mixed-name-and-subscript-targets)
relates accepted targets and a bounded RHS to independent lexical rules.
The block collection theorem below supplies that environment and write
scope for its admitted forms. A separate theorem covers capture selection
and installation for one bounded nested function. Whole-module
elaboration against independent source rules and text parsing remain open.
Lambdas, general comprehension expression
positions, field leaves, store leaves in loop and comprehension targets,
and other augmented assignment forms remain outside this source fragment.
The pinned Starlark spec rejects slice assignment targets.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Resolve/Thms.lean) · [Lean source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

Pinned Starlark-Go checks cover static and dynamic name errors, captures,
defaults, load aliases, and loop scope and control. Go rejects the
load-then-global collision and accepts the global-then-load order. The Lean adapter follows the
Bazel-team spec and rejects both.
[Pinned Go comparison](../../examples/starlark/scope/check.go) · [Name binding in the pinned spec][names]

### Lexical block collection

`ModuleBinders` and `BodyBinders` state which normalized commands and
statements declare names, with their occurrences in source order. The
load-free module subset covers name assignment, mixed patterns,
ordinary subscript stores, expression statements and definitions. The
function subset also covers pass, return, sequences and both branches of
a conditional. A definition binds its name in the current block. Its
parameters, defaults and body do not contribute binders there. A nested
block can be collected separately using the parent's read context.

In a mixed pattern, only a name leaf contributes a declaration. A
receiver, subscript index, RHS and comprehension generator contribute no
declaring occurrence in the surrounding block. `ParameterBinders` follows
the normalized parameter classes. `LocalBinders` keeps the first occurrence
of each other body binder. An assignment to a parameter reuses its slot.
`owned_read` selects a body binder's owned slot even before its first
assignment and even when an enclosing or global name has the same
spelling. An uninitialized slot fails when read.

`moduleBlock_eq` and `collectFunctionLayout_eq` prove the existing
compiler's collection and write-scope phases agree with the declarative
rules. `module_assignment_sound` and `function_assignment_sound` compose
with the independent mixed-assignment elaboration theorem and put each
resolved name leaf among the declared globals or owned slots. Assignment
elaboration still uses the bounded leaf and RHS grammar. The block rules
cover declaration occurrences only. Identifier, parameter, duplicate
global and runtime validation remain in the existing checked entry point.

The function collection theorem takes the parent context as input.
Whole-source execution, unproved binder grammar including load aliases
and loop targets, and broader leaf and RHS elaboration remain open.
[Block judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Block/Checks.lean)

### Nested function captures

The capture theorem covers one immediate enclosing function in a load-free
module. The inner function has required positional parameters and a body
consisting of `(name, receiver[index]) = rhs` followed by `return operand`.
The leaf and return operands use the bounded #3171 grammar. The RHS is a
plain operand or a single-generator list comprehension in that grammar.
`parent_layout` supplies the outer function's owned names and inherited
module globals from the proved block collector.

`BodyReads` gives the binding occurrences of the RHS, target and return,
in that order. `Selects` ignores owned parameters and locals, takes a
read from the immediate parent's owned slot when it exists, and otherwise
uses the declaring module's global. It retains the first occurrence of
each free reference in the Lean declaration. The comprehension generator
contributes no free read of its own binding. `mixed_definition` connects
these rules to the exact declaration appended by the compiler. Go uses
cells for enclosing free variables and carries the module's global
dictionary separately. The Lean list represents just the module slots
that are read. Its order is a Lean representation property.

`define_installs` relates selected addresses in the defining activation
to the new heap cell and the binding holding its function reference.
Restoring the caller preserves that cell. `activate_selected` preserves
the installed addresses while allocating the callee's own slots.
Creation consults the slot address. Reading an uninitialized binding
through that address fails when invoked. `read_after_rebind` states that
a write by the slot's owner is then visible to that callee. A list store
through the captured value instead changes the list's heap cell. Both
observations agree with the pinned spec's free-variable references and
the pinned Go fixtures.

The runtime theorem takes the defining frame's slot mapping as evidence.
Forwarding locals through additional function levels, correspondence for
broader bodies and definition-time defaults, and independent whole-source
execution remain open.
[Judgments](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Defs.lean) · [Theorems](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Thms.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Capture/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/scope/check.go) · [Pinned definition semantics](https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#function-definitions) · [Go lexical selection](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/resolve/resolve.go#L960-L990) · [Go shared cells](https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/interp.go#L642-L661)

## Finite-manifest loader

`Loader.load` takes a known module ID and an optional session. A session
keeps the shared runtime and the cache for one fixed manifest and linked
declaration table. Manifest array indices are canonical IDs. Each entry
provides its own label table, queried when that module executes a load.
Distinct labels that resolve to the same ID share one successful
initialization and the published values retain their heap identities.
The table uses the first matching label when entries repeat.
The linked declaration table is supplied up front and its signatures and
bodies are checked by the shared module validator. Each source's own
commands, allocations and publication are processed on demand.
[Loader definitions](../../Silmaril/Languages/Starlark/Modules/Loader/Defs.lean)

- A missing label reports the requester and label. An ID outside the
  manifest reports an unknown module when it is requested.
- A cycle reports the current path from the root through the repeated
  ID. The path is local to the request and is discarded when it ends.
- Validation and runtime errors carry the ID of the failing module.
  A missing export is a failure of the importing command. Failure stops
  the remaining commands and propagates to every waiting importer.
- Failed modules leave no cache entry and perform no publication freeze.
  Prior heap effects and successfully published dependencies survive,
  so a later request can retry the failure and reuse those dependencies.
  Callers recover their lexical and iterator state at each module exit.

`runs_iff_denote` proves exact agreement with independent rules on the
result, error, heap and cache. Descent counts inactive manifest IDs and
pending commands, so the loader needs no fuel. A fresh Starlark thread
and publication freeze use the same primitives as `initializeModule`.
Canonical resolution, successful-publication caching and cycle rejection
are policies of this host model. Filesystem I/O, concurrency, custom host
thread state, failure caching and backtraces remain open.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Loader/Thms.lean) · [Load statements][loading] · [Module execution][modules]

The Go loader fixture supplies the same host policy through `Thread.Load`.
It uses `Program.Init` and freezes globals only on success. This lets it
compare dependency order, aliases and failure effects in the pinned
engine. The cycle and cache policy come from the fixture's host, and the
Go convenience wrapper freezes a partial mapping even on failure.
[Lean loader fixtures](../../Silmaril/Languages/Starlark/Modules/Loader/Checks.lean) · [Go loader fixtures](../../examples/starlark/loader/check.go)

The Lean fixtures cover cross-module captures, private freezing, file-local
aliases, validation, missing exports and failure restoration. The native
fixtures check source order, skipped branches, absent assignment after an
effectful error, and the freeze of exported aliases, their nested values and
reachable function defaults. The pinned Go fixtures compare successful
publication through `ExecFileOptions` and observe failure effects through
`Program.Init`. Go's convenience wrapper also freezes the partial global
mapping on error. The Lean failure and loader fixtures check the shared
heap and absence of publication on failure under the pinned prose policy.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Checks.lean) · [Native fixtures](../../Silmaril/Languages/Starlark/Modules/ExpressionChecks.lean) · [Go fixtures](../../examples/starlark/modules/check.go) · [Pinned starlark-go][go]

```sh
lake build --wfail +Silmaril.Languages.Starlark.Modules.Checks \
  +Silmaril.Languages.Starlark.Modules.ExpressionChecks \
  +Silmaril.Languages.Starlark.Modules.Loader.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.Checks \
  +Silmaril.Languages.Starlark.Modules.Resolve.LoopChecks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/modules/check.go" && go run "$fixtures/loader/check.go" &&
  go run "$fixtures/scope/check.go")
```

[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[expressions]: starlark-functions.md#direct-denotation-of-resolved-expressions
[source-expressions]: starlark-functions.md#resolving-a-normalized-expression
[subscript-assignment]: starlark-functions.md#simple-subscript-assignment
[pattern-assignment]: starlark-functions.md#standalone-pattern-assignment
[augmented-subscript]: starlark-functions.md#integer-augmented-subscript-assignment
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-binding-and-variables
[loops]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#for-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
