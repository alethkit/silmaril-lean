# Bounded exact-key GVN for pure Sea of Nodes

`Silmaril.SSA.SeaOfNodes.GVN.Pass.run` repeats one checked deletion at a
time over the pure acyclic `Diamond.Dataflow` table. Each step visits
candidates in table order and asks discovery for the oldest matching
producer before that candidate. It brings the representative’s typed
wire into the candidate’s operand scope, where elimination checks that
it identifies the same representative. After deletion, the next scan
uses the shorter table and its rewritten operand addresses.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/GVN/Pass/Defs.lean) ·
[Discovery](sea-of-nodes-gvn-discovery.md) ·
[Elimination](sea-of-nodes-gvn-elimination.md)

## Verified contract

- `step?_eq_none_iff` says a scan fails exactly when the checker accepts
  no pair in the current table. Every matching candidate has a
  representative in its operand scope and can pass the deletion
  check with that wire.
- `step_size` says each successful scan removes exactly one binding.
  `run_progress` counts those deletions exactly. The remaining length
  plus the deletion count equals the original length, and the deletion
  count is at most the input fuel.
- `run_sound` preserves the value read at every original typed wire,
  using the returned composition of the individual routings. This
  covers all surviving and deleted results and any selected return
  wire, in every pure total model and under every argument and
  initial-scope assignment.
- `run_normal_of_remaining` proves the returned table has no
  checker-accepted pair if the deletion count is strictly below the
  fuel. Exhausting fuel returns the current table and its routing.
  `normalize` supplies the original binding count plus one unit of
  fuel. Exact shrinkage leaves room for a final scan, so
  `normalize_normal` establishes the same property after recomputing
  keys in the resulting table.

[Public theorems](../../../../Silmaril/SSA/SeaOfNodes/GVN/Pass/Thms.lean)

## Regression and scope

Two bindings compute `x - y`. Two downstream bindings subtract `x`
from those different addresses and initially have different keys.
Deleting the first duplicate makes the downstream bindings read the
same address. The regression checks that discovery finds the second
match only after that redirection. One unit of fuel returns the
intermediate table. Normalization makes two deletions, preserving the
distinct reversed subtraction. With `x = 10` and `y = 3`, the two
downstream operand orders still give `-3` and `3`.
[Lean regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Pass/Regression.lean)

Normal form here is relative to the existing exact structural-key
checker and the producer bindings in the supplied table. Initial
scope wires can supply operands. The pass rescans and recomputes keys
after each deletion. Hashing complexity, cyclic refinement, algebraic
identities, constant folding, and control placement remain separate.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Pass.Regression'
```

## Source

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
pp. 246–257, §3.1, step 3. The pass combines that step’s exact
opcode-and-input lookup, use replacement, and removal on the supported
table. The archived UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf)
