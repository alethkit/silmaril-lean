# Starlark module publication and imports

The profile follows the Bazel-team core specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. Raw `spec.md` has SHA-256
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Module execution][modules] · [Load statements][loading]

`Silmaril.Languages.Starlark.Modules.Thms` exposes the resolved entry point
`initializeModule`. It checks argument-list legality and conflicting global
and file names before allocating slots. It executes top-level commands in
order. The supported commands are collection assignments and expression
statements, resolved definitions and calls, and load statements with named
aliases. Function-only control lives within declarations. Clients supply
declared globals and resolved assignments, including single assignment of
explicit globals and legal load identifiers. Temporary slots used by call
lowering and file-local imports remain outside the global export list.
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

`initializes_iff_initialize` proves exact agreement with independent
command-sequencing and initialization rules on publication, failure and final
state. Core top-level commands use the existing independent function and
collection judgments. The rules use the same host catalog contract as the
denotation. The finite-manifest loader adds on-demand initialization to
this shared publication model.
[Operational rules](../../Silmaril/Languages/Starlark/Modules/Operational/Defs.lean) · [Theorem header](../../Silmaril/Languages/Starlark/Modules/Thms.lean)

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
aliases, validation, missing exports and rollback of the scope on failure
while retaining prior effects. The pinned Go fixtures compare successful
publication, import observations and failure categories. They use Go's
`ExecFileOptions` success path for publication. The Lean-only failure fixture
asserts the absence of a publication freeze after failure, following the
prose spec. Go's convenience wrapper also freezes the partial global mapping
on error.
[Lean fixtures](../../Silmaril/Languages/Starlark/Modules/Checks.lean) · [Go fixtures](../../examples/starlark/modules/check.go) · [Pinned starlark-go][go]

```sh
lake build --wfail +Silmaril.Languages.Starlark.Modules.Checks \
  +Silmaril.Languages.Starlark.Modules.Loader.Checks
```

Use Go 1.25 or newer and run from the repository root.

```sh
fixtures="$(pwd)/examples/starlark"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixtures/modules/check.go" && go run "$fixtures/loader/check.go")
```

[modules]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#module-execution
[loading]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#load-statements
[go]: https://github.com/google/starlark-go/tree/4f4267fb140d1e8b91c9bce55cee2f809e8840dd
