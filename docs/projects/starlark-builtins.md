# Starlark universal built-in calls

This profile follows the Bazel-team specification at
`c0af0ea03dc90d3bbc021394b693e6957cc15030`. The raw `spec.md` SHA-256 is
`9e1e2b52717512968270bc99ca79aa8c9014df99a9befd0b47eed59c7c848597`.
[Built-in functions][builtins] · [Name resolution][names]

## API and observations

`Lists.Builtin.resolve` maps supported universal names to typed IDs after
lexical lookup has ruled out a shadowing binding. A resolved `Lists.Code.builtin`
expression denotes the first-class value for that ID. It can be stored,
captured, passed as an argument, called through a local binding, or used as a
dictionary key. Its key encodes the universal ID and its truth value is true.
It has no heap allocation or reachable cells of its own. The scalar resolver
and the existing resolved collection constructors retain their entry points.
[Shared value and syntax definitions](../../Silmaril/Languages/Starlark/Lists/Defs.lean)

The existing call evaluates the callee and operands left to right, expands
`*` and `**`, and dispatches on the resulting callable value. For these
built-ins, a nonempty expanded keyword list fails before arity or operand
type checks. For example, an empty `**{}` expands to no keywords. Errors
carry the built-in ID and the offending keyword, arity bounds or value.
Earlier operand effects persist on failure, and the call destination is
written only on success. Built-in dispatch uses no lexical activation or
declaration-stack entry.
[Call definitions](../../Silmaril/Languages/Starlark/Functions/Defs.lean)

| Built-in | Positional arguments | Values and store |
| --- | --- | --- |
| `bool` | Zero or one | Existing truth rules for all supported values. The zero-argument result is `False`. |
| `len` | Exactly one | List, tuple or range length, dictionary entry count, or string byte length. Other represented types give a type error. |
| `type` | Exactly one | A string naming the existing value tag, including `NoneType`, `function` and `builtin_function_or_method`. |
| `list` | Zero or one | Allocates a fresh mutable list. The optional iterable is a list, tuple, dictionary or range. |
| `tuple` | Zero or one | Returns an immutable tuple over the same iterable domain. The internal tuple cell carries its structural key when hashable. |
| `range` | One to three | Checks integer parameters in order, rejects a zero step, and returns an immutable range without allocating a heap cell. |

Dictionary iteration yields keys in insertion order. Both constructors make
shallow snapshots, retaining the identities of referenced elements.
Copying a frozen list can produce a mutable outer list with frozen elements
still shared. The built-ins only read input cells. They run no Starlark code
while copying, and leave the active-iterator stack alone. The three
inspection built-ins and `range` leave the heap alone after operand evaluation.
[Built-in definitions](../../Silmaril/Languages/Starlark/Functions/Builtins/Defs.lean)

## Materializing ranges

`list(range(...))` and `tuple(range(...))` consume the same exact cursor as
a function-body loop, in yield order. The cursor is collected only after
the operand and the call's expansion, keyword and arity checks succeed.
The constructor then adds one result cell using the existing list or tuple
allocation rule, including for an empty range. A rejected call retains
earlier operand effects and adds no result cell. The range is immutable,
and reading it changes neither the heap nor active iterator guards.
[Pinned list spec][list] · [Pinned tuple spec][tuple] · [Pinned Go list][go-list] · [Pinned Go tuple][go-tuple]

Materializing a range takes time and storage proportional to its length
in elements, with exact integer arithmetic for cursor steps. The denotation
terminates by the remaining count. There is no language-level size cutoff
or fuel error. Executing large materializations depends on host memory.
The Go implementations preallocate for their host-width range length.
The common-profile fixture uses small ranges, and the Lean fixture includes
a short range with exact endpoints outside Go's host integer width.
[Cursor definition](../../Silmaril/Languages/Starlark/Lists/Iteration/Defs.lean) · [Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Pinned Go fixtures](../../examples/starlark/builtins/check.go)

`Builtins.invoke` is total over expanded arguments and the current state.
`invokes_iff_invoke` proves its exact result, error and store agree with the
independent built-in rules. The range rule uses `CursorCollects`, whose yield
order agrees with collection by `cursorCollects_iff_collect`. The call proofs
compose these rules with operand evaluation in `exec_iff_denoteBody` and
preserve the exact heap and visible bindings under scratch projection in
`lower_preserves`.
[Operational rules](../../Silmaril/Languages/Starlark/Functions/Builtins/Operational/Defs.lean) · [Built-in theorem](../../Silmaril/Languages/Starlark/Functions/Builtins/Thms.lean) · [Cursor theorem](../../Silmaril/Languages/Starlark/Lists/Iteration/Thms.lean) · [Lowering theorem](../../Silmaril/Languages/Starlark/Functions/Lowering/Thms.lean)

## Dialect and coverage

The spec permits 8-bit or 16-bit string elements. This profile selects
UTF-8 byte lengths, as pinned starlark-go does. For example, `len("é😀")`
is 6 in both. The Lean input uses Unicode text, while Go strings can also
hold invalid encodings. Both reject plain strings as iterable constructor
inputs. Keyword-before-arity rejection follows the pinned Go implementation.
The fixtures compare values, aliases and error categories. The existing
argument-signature and module-failure differences remain recorded in their
guides.
[Strings][strings] · [Pinned Go built-ins][go-library] · [Arguments](starlark-functions.md#argument-binding) · [Modules](starlark-modules.md)

Range spreading and loop destructuring remain separate. Additional
value types include bytes, sets and iterable views,
floats and host values. The other pinned universal
functions are `abs`, `any`, `all`, `bytes`, `dict`, `dir`,
`enumerate`, `fail`, `float`, `getattr`, `hasattr`, `hash`, `int`,
`max`, `min`, `print`, `repr`, `reversed`, `set`,
`sorted`, `str` and `zip`. General bound-method dispatch is open. The
existing collection `append` primitive remains available through its
resolved collection syntax. The coverage guide lists the remaining methods.
[Lazy range subscript reads](starlark-functions.md#lazy-range-subscript-reads) · [Coverage obligations](starlark.md#coverage-obligations)

## Checks

```sh
lake build --wfail +Silmaril.Languages.Starlark.Functions.Builtins.Checks
```

Run from the repository root with Go 1.25 or newer.

```sh
fixture="$(pwd)/examples/starlark/builtins/check.go"
oracle="$(mktemp -d)"
git clone https://github.com/google/starlark-go.git "$oracle"
git -C "$oracle" checkout --detach 4f4267fb140d1e8b91c9bce55cee2f809e8840dd
(cd "$oracle" && go run "$fixture")
```

[Lean fixtures](../../Silmaril/Languages/Starlark/Functions/Builtins/Checks.lean) · [Go fixtures](../../examples/starlark/builtins/check.go)

[builtins]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#built-in-constants-and-functions
[names]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#name-resolution
[strings]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#strings
[list]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#list
[tuple]: https://github.com/bazelbuild/starlark/blob/c0af0ea03dc90d3bbc021394b693e6957cc15030/spec.md#tuple
[go-list]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L679-L696
[go-tuple]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go#L1124-L1143
[go-library]: https://github.com/google/starlark-go/blob/4f4267fb140d1e8b91c9bce55cee2f809e8840dd/starlark/library.go
