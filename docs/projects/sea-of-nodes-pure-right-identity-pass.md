# Discover and erase explicit word identities

The shared checker implements the right-hand integer cases `x - 0`,
`x + 0`, and `x * 1` from Simple chapter 8. This pass invokes that
checker on a typed pure program without requiring a caller to select
an opcode, binding, or literal.
[Shared checker and modular model](sea-of-nodes-pure-right-identities.md) ·
[Pinned SubNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/SubNode.java#L31-L40) ·
[Pinned AddNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L39) ·
[Pinned MulNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/MulNode.java#L27-L40)

`RightIdentityPass.step?` visits the typed word producers in table order.
For each applicable binary shape, it recovers that binding's actual
right-hand wire from the prefix and scans the current word origins for
its exact address. The shared checker still decides whether the
source is the required explicit literal and performs the erasure.
Each successful step discards the old enumeration. The next scan
uses the shortened table and its redirected wires.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/RightIdentityPass/Defs.lean)

- `step_checked` ties every successful step to the shared checker.
  `step_size` shows one fewer producer, and `step_eval_eq` shows
  the same native result at every typed input.
- `run_progress` proves that the new table length plus the number of
  deletions equals the old length, and that deletions are bounded by
  the fuel. `normalize` uses the original length plus one, leaving
  room to search after the last possible deletion.
- `step?_eq_none_iff` is exhaustive over every nomination the shared
  checker could accept in the current table. `normalize_normal` gives
  that property for the final program, and `normalize_eval_eq` gives
  its return equality for all typed inputs in the 64-bit model.

The fixture eliminates `1 + 0`, exposing a literal `1` on the right
of a multiplication. The next scan removes that multiplication and
redirects a downstream addition. The exact shortened table and
shifted return are checked. A surviving `0 - y` exercises the ordered
near miss, and the final return checks wraparound for inputs 0 and 1.

The normal form is relative to the three explicit right-hand literal
rules in a pure straight-line table. The scan does not infer constants,
commute operands, or remove unused literal bindings.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/RightIdentityPass/Thms.lean) ·
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/RightIdentityPass/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero.RightIdentityRegression +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.RightIdentityPass.Regression
```
