# Discover one shrinking cyclic GVN step

`Cyclic.Pass.step?` takes a certified activation view of the current
`Loop.Graph`. It computes the stable partition with `FixedPoint.normalize`
and tries typed proposals without a caller-supplied candidate. A success
is a loop with one fewer header producer.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Pass/Defs.lean) ·
[Stable partition](sea-of-nodes-gvn-cyclic-fixed-point.md) ·
[Certified view](sea-of-nodes-gvn-cyclic-activation.md)

## Proposal space

1. Try direct deletion of every header producer in table order.
2. Walk every actual header producer and its ordered operand occurrences.
   The current wire identifies the original source by its typed address.
   For each same-sort output in the consumer's actual prefix, use the
   certified view to find represented sources at that output address.
   The prefix enumeration starts with no producer outputs and extends
   the typed addresses after each preceding binding.
3. Run `HeaderUse.redirect?` on each proposed edit. If it accepts, scan
   the edited header in table order with `Deletion.delete?`. Return a
   result only when this second check also accepts. It checks surviving
   header uses, the guard, the complete feedback tuple, and the exit.

The first successful proposal wins. The redirects use earlier header
outputs as representatives and require the old and replacement sources
to be represented in the supplied view. Direct deletion covers the whole
header even if some producers are absent from the view.
[Header-use checker](sea-of-nodes-gvn-cyclic-header-use.md) ·
[Deletion checker](sea-of-nodes-gvn-cyclic-deletion.md)

## Checked contract

- `step?_accepted` identifies an enumerated proposal that produces the
  returned loop through the existing checks. `step_count` proves exact
  one-producer shrinkage.
- `step_initial` preserves the initial tuple. `step_activation` preserves
  the full activation transition on old tuples satisfying the original
  view's class invariant. `step_evalBackedges` and `step_returns` preserve
  all bounded evaluations and finite returns from entry.
- `step?_eq_none_iff` characterizes failure as exhaustion of this exact
  proposal list at the view's computed partition. The inner deletion
  scan covers every typed producer of its supplied header, as shown by
  `firstDeletion?_eq_none_iff`.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Pass/Thms.lean)

## Regression and scope

On the deletion fixture, the search finds the guard redirect and shrinks
the header from four producers to three. The result returns 4 after two
backedges. In a variant, both equivalent increment producers are live on
the feedback column. The same local redirect is accepted and the
whole search returns `none`. The feedback uses prevent both increments
from being dropped.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Regression.lean)

The result is one shrinking step. Repeating the search with cyclic
redirects needs a fresh certified view of the new loop. Its producer
references, operand keys, and Phi and observation correspondences must
match the edited table and shifted addresses. The step computes
partitions and proposals for a supplied view. It leaves view extraction,
multi-use redirection, and iteration across changed views outside this
scope. Exhaustion is relative to the enumerated proposals and says
nothing about larger edits that could unlock a later deletion.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Pass.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Regression
```

## Sources

Cliff Click, *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1, step 3, identifies a matching producer, redirects uses, and removes
the redundant binding. This increment enumerates single-use edits and
requires an actual one-binding deletion to return a result. The archived
UW PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
[Proceedings](https://doi.org/10.1145/207110.207154) ·
[Archived PDF](https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf)

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2, supplies the cyclic
congruence that the existing fixed-point checker computes. The search
uses the ordered typed class keys of that checker for the current view.
[Rice record](https://hdl.handle.net/1911/16807)
