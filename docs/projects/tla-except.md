# Mathematical TLA+ EXCEPT paths

Import [`Data.Tagged.Except.Thms`](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Except/Thms.lean)
for mathematical paths and clauses over the
[tagged function values](tla-functions.md). The evaluation input is a root
value, ordered value keys and a replacement of type `Value → Value`.
The argument to that replacement is the old leaf denoted by `@`.
Compute the keys in the enclosing valuation. Each replacement closes over
that valuation and receives its own old leaf.
Source syntax requires at least one key. The mathematical recursion
uses the empty path to look up or replace the root.

## Clause and path semantics

In *Specifying Systems* §16.1.7, p. 304, a single update
`[f EXCEPT ![d] = e]` retains `DOMAIN f` and binds `@` in `e` to `f[d]`.
The rule for `![d1]...[dk]` applies the remaining path update to the old
child at `d1`, then replaces that child. At the final segment `@` is the
old leaf at the full path. The multiple-clause rule passes the result of
the first `n - 1` clauses as the head of clause `n`. Thus a later
clause reads the value entering that clause, including earlier updates.
For a key whose initial value is 10, two clauses at that key with
right-hand side `@ + 1` read 10 and 11 and leave 12.
[Book §16.1.7, p. 304](https://lamport.azurewebsites.net/tla/book-21-07-04.pdf#page=322)

Pinned SANY associates a bare `@` with the innermost active clause.
It generates a nested EXCEPT head and its path components in the
enclosing context, then installs the inner binding for that clause's
replacement expression. Dot components become string keys and a comma
index becomes one tuple key. SANY's `AtNode.levelCheck` inspects the
head and earlier clauses, stopping at the current clause. Its level
bookkeeping is a separate frontend contract from substitution of a
full mathematical leaf expression, which includes the current path
keys. Scope, key lowering and levels belong to Resolution and DataElab.
This module consumes the results of those steps.
[Pinned SANY generator](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/Generator.java#L4168)
· [Pinned SANY level check](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tla2sany/semantic/AtNode.java#L80)

Pinned TLC's `Tool` evaluates the keys in the enclosing context, calls
`result.select(path)` on the running result, then evaluates the RHS
with that leaf bound and calls `takeExcept`. This agrees with the
book's ordered clauses on valid paths. If selection reports a missing
component, TLC warns and skips the RHS. The mathematical law likewise
preserves the root. The denotation has no diagnostic or observable RHS
evaluation. TLC's path selector rejects a
non-function ancestor, and its record selector can reject a non-string
key. In the tagged model a record is a graph whose domain contains
string values, so a nonmember key gives a missing key. For a
non-function ancestor the tagged mathematical interpreter instead
composes the existing configurable application and update results.
The book's expansion uses `DOMAIN` and application, whose values on
non-functions are outside its function laws. The tagged policy on such
inputs is a chosen extension, distinct from TLC's error behavior.
[Pinned TLC clause loop](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tlc2/tool/impl/Tool.java#L2300)
· [Pinned TLC path selection](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tlc2/value/impl/Value.java#L319)
· [Pinned TLC record selection](https://github.com/tlaplus/tlaplus/blob/bc1b506bdcad80bb518bf3776a9161c34ff0fc4c/tlatools/org.lamport.tlatools/src/tlc2/value/impl/RecordValue.java#L509)

## Checked interface

| API | Law |
| --- | --- |
| `Value.lookupPath root keys` | Classifies a recognized path as a found leaf, a missing key or a non-function ancestor without consulting the fallback policy. |
| `updatePath_single` | A singleton path uses the existing `Value.apply` to obtain the old component and `Value.update` to replace it. |
| `updatePath_through_key`, `lookupPath_update_found` | Rebuild the recognized parent from the recursive child update. If the original path found leaf `v`, the same path in the result finds `replacement v`. |
| `updatePath_missing`, `updatePath_nonfunction` | A missing key reached through recognized functions preserves the root. A non-function step uses the same fixed `.apply` and `.update` operations as single-key evaluation. |
| `domain_updatePath_function`, `lookupPath_update_sibling` | Replacing a child preserves the parent's exact domain and every path starting at a different key. The same laws apply at an inner parent through the recursive equation. |
| `Value.updateClauses policy root clauses`, `updateClauses_cons`, `updateClauses_append` | Left fold on the incoming root with the clause's own path and replacement. Evaluating two lists in sequence agrees with evaluating their concatenation. |

The [Lean examples](../../Silmaril/Logic/Temporal/TLA/Data/Tagged/Except/Examples.lean)
check the duplicate nested update, an untouched record field, a missing
inner key and the mathematical non-function policy. These are
denotations for already resolved paths and RHS closures. Source
acceptance and correspondence with a frontend are separate work.

```sh
lake build --wfail +Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Thms \
  +Silmaril.Logic.Temporal.TLA.Data.Tagged.Except.Examples
```
