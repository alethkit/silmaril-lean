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
a `CompExpr` right-hand side.
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
nested name patterns, operands of standalone subscript stores, and
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
AST with legal identifier spellings. An independent source binding relation
and text parsing remain open. Lambdas, general comprehension
expression positions, subscript or field leaves in patterns, and other
augmented assignment forms remain outside this source fragment.
The pinned Starlark spec rejects slice assignment targets.
[Theorem header](../../Silmaril/Languages/Starlark/Modules/Resolve/Thms.lean) · [Lean source fixtures](../../Silmaril/Languages/Starlark/Modules/Resolve/Checks.lean)

Pinned Starlark-Go checks cover static and dynamic name errors, captures,
defaults, load aliases, and loop scope and control. Go rejects the
load-then-global collision and accepts the global-then-load order. The Lean adapter follows the
Bazel-team spec and rejects both.
[Pinned Go comparison](../../examples/starlark/scope/check.go) · [Name binding in the pinned spec][names]

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
