# Invoke the prepared SQLite reactor initializer

`SqliteWasm.reactorPreparedInvocation` proves that the ordinary Core
configuration produced by `prepareDirect? evalConst?` for the canonical
23-entry typed fixture exports `_initialize` at address 25. The resolved
function is invokable with no arguments. The theorem identifies the
resolved memory at index 0 before invoking the function. Core `invoke`
reduces to no values and an empty outer frame. The proof gives the exact
memory update, an initialization mark followed by the eight setup
writes. It is quantified over the Core numeric profile and host relation.

The result uses the original SQLite reactor quotation, ordinary segment
application, and the linked invocation theorem. The prepared module
has absent Start. A separate validated instantiation theorem requires
the independent module typing judgment and compatible external addresses.

Use the same generated directory as the whole-module fixture.
[Whole-module fixture recipe](../whole-module/README.md#reproduce)

Run the prepared-invocation check.

```sh
bash tools/sqlite-wasm/prepared-invocation/check.sh /path/to/lean/SqliteWasm
```
