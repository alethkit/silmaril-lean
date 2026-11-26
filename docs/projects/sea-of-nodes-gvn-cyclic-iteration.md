# Rebuild and repeat cyclic GVN on a native loop

`Iteration.normalize` runs the native `Builder.optimize?` step on the
current typed `Loop.Graph`. Each success removes one header producer.
The next call rebuilds the view from the shortened table, including its
shifted origins and actual Phi columns. When a step returns `none`, the
driver returns its current loop and the count of successful deletions.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Defs.lean) ·
[Native view builder](sea-of-nodes-gvn-cyclic-builder.md) ·
[One-step search](sea-of-nodes-gvn-cyclic-pass.md)

## Termination and observations

- `run_progress` proves exact accounting for any deletion fuel.
  The final header length plus the reported deletion count equals
  the original length. The count is at most the given fuel.
- `run_stops_of_fuel` proves that fuel at least the initial header
  length suffices. Each accepted step consumes one unit of fuel and
  removes exactly one binding. If all that fuel is spent, the header
  is empty and another successful deletion would contradict the
  one-binding decrease theorem.
- `run_evalBackedges` preserves evaluation at the same backedge budget,
  including exhaustion. `run_finite_returns` preserves and reflects
  finite returns. Both compose the native one-step theorems at each
  successful rewrite. The default-run corollaries give these guarantees
  for `normalize`.
- `normalize_no_candidate` assumes a successful fresh view build on
  the final loop. It then rules out every accepted shrinking proposal
  in that view's enumeration. A refused view build is also a stop
  condition. Calling the builder on the final loop distinguishes them.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Iteration/Thms.lean)

## Regression and scope

A native loop carries two latches with the same feedback. Its header
has three equivalent increments. One feeds the latches, one feeds the
guard, and one feeds the exit computation. The first native step
redirects the guard operand and shrinks the header from five bindings
to four. A fresh build finds the second redirect and shrinks it to
three. The final loop remains buildable and returns 4 after two
backedges. One backedge of budget still yields `none`. A separate test
keeps the original loop when a Phi entry reads a preheader producer.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Regression.lean)

The result is relative to the existing direct-argument-entry builder
and the search's direct deletions and single-use redirect/delete
proposals. The terminal theorem ranges over those proposals on the
final admitted view.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Defs
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression
```

## Sources

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1, step 3, redirects redundant uses and removes the redundant
binding as the optimizer processes its worklist. This driver repeats
the library's checked single-binding step and builds each cyclic view
from the resulting typed loop.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Search source correspondence](sea-of-nodes-gvn-cyclic-pass.md)
