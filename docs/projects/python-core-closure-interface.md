# Python closure compiler runtime interface

The compiler-facing environment lives in
`Silmaril.Languages.Python.Core.Closure`. The runtime represents exact
integers and functions with a code-table key and ordered captured cell
identities. A `CodeRef` records its expected frame layout. The compiler
supplies the layout and the mapping from source bindings to bounded
slots. [Lean definitions](../../Silmaril/Languages/Python/Core/Closure/Defs.lean)

## Slots and captures

| Interface | Compiler use |
| --- | --- |
| `Layout`, `Slot layout` | Count direct locals, owned cells and incoming captures. Each slot is a `Fin` of the corresponding count. |
| `ParameterSlot layout`, `Parameters layout` | Supply direct-local or owned-cell parameter destinations in declaration order, with no repeated destination. |
| `Frame.fresh`, `Function.freshFrame` | Initialize unbound direct locals and allocate fresh owned cells. Incoming captures keep their supplied identities. |
| `Frame.read`, `Frame.write` | Load or update a slot. Cell updates return the residual shared heap and preserve the frame's slot-to-cell mapping. |
| `Frame.closure`, `Function.ofCaptureList` | Create a closure in child capture order using a bounded parent-slot map or an ordered list with its length proof. |

The source layout checker can use `Frame.owned` and `Frame.captures` for
its owned and forwarded lookups. Each has type `Fin count → CellId`.
The list interface can consume the resulting capture list and its length
proof directly. Source resolution establishes which indices correspond to
which bindings. The runtime preserves addresses and their order independently.
[Source layout candidate #2253](https://github.com/hiloopai/silmaril-lean/pull/2253)

Theorems establish freshness and disjointness of owned allocations, preservation
of existing cells during allocation and writes, ordered capture lookup and
readback through an alias. An allocated unbound cell differs from an invalid
address. Incoming unbound reads correspond to Python `NameError`. Unbound
direct local and owned-cell reads correspond to `UnboundLocalError`.
[Theorems](../../Silmaril/Languages/Python/Core/Closure/Thms.lean)
· [Regression](../../tests/languages/python/closure-runtime/Regression.lean)

## Call and stack stages

The call stage will bind a list of fixed positional arguments in order to the
distinct `Parameters.slots` of a fresh frame. Arity mismatch is a defined
error and has no committed allocation or write. The binding proof will
identify each bound argument, preserve the incoming identities and show that
other fresh destinations remain unbound.

The stack stage will save the caller frame and its continuation before
entering the callee. A return restores both with the residual heap and passes
the value to that continuation. A defined error also preserves the saved
frame and residual heap and passes the error to the corresponding unwind
continuation. The preservation claim covers direct locals and the identity
mappings in the saved frame. The residual heap supplies the latest values of
shared cells. The interface reserves `Result` for normal returns and defined
Python errors. Invalid cell addresses are separately classified by `Failure`.
Keyword arguments, default values, variadic binding and exception-handler
execution require additional profiles.

The public baseline is the Python 3.12.13 language reference. The Data model
HTML has SHA-256 `c300d0904a1a03abd7752308eacffbdf7364d95d45f8e52d60076f38a21f763e`.
The Execution model HTML has SHA-256
`1928f7f11bbb47a652c55a292cb90bbd5c07224e0c6ddf019445ae653cd64102`.
The Expressions HTML has SHA-256
`d8c992b1815b59ba65aa9a0144bf2f0a24a3551cda8cbb06f5e76c5caec7d994`.
[Closure cells](https://docs.python.org/release/3.12.13/reference/datamodel.html#function.__closure__)
· [Name resolution](https://docs.python.org/release/3.12.13/reference/executionmodel.html#resolution-of-names)
· [Calls](https://docs.python.org/release/3.12.13/reference/expressions.html#calls)

```sh
lake build --wfail +Silmaril.Languages.Python.Core.Closure.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/languages/python/closure-runtime/Regression.lean
```
