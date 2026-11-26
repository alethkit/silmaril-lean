# The Schedule Late bound on a typed CFG

In PLDI ’95 §2.3, pp. 250–251, Click computes the lowest common ancestor of
an instruction's use blocks in the dominator tree. A Φ input counts as a
use in the predecessor block for that input's CFG edge. This implementation
computes the bound for an already supplied list of uses. It uses the same
read cuts as the existing placement checker. [Proceedings][paper] ·
[Archived PDF][pdf] · [Coverage matrix][coverage] · [Placement legality][legality]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
Its Schedule Late pseudocode takes the common ancestor after scheduling
each use. Here, `resolveUses?` pairs each incoming occurrence with its
existing read cut and validates the cut. A Φ use retains its source, slot
and argument index. Parallel slots may resolve to the same terminator cut
and still occupy distinct entries in the result.
[Definitions][defs] · [Theorem header][theorems]

`lateBound?` scans the finite inventory for reachable blocks whose
addresses prefix every read address and selects the longest such address.
The synthesized tree supplies exact ancestry on the original CFG.
`lateBound?_spec` proves that, with a closed inventory and complete tree
evidence, a block dominates the result exactly when it dominates all
resolved read blocks. A nonempty valid use list yields a bound.
`some none` denotes the anonymous entry. [Tree synthesis][synthesis] ·
[Theorem header][theorems]

`legal_iff_lateBound` rewrites the use-block dominance part of the existing
legal corridor to dominance of the bound. The candidate must still follow
its operand cuts and precede each read in the same block. The theorem
concerns legality for the supplied cuts and uses. The existing placement
API supplies cut enumeration and ranking. [Theorem header][theorems]

## Example

The public fixture has a named fork followed by a diamond. Both branch
slots at `left` target the join and carry different operands. The first
bound for those uses is `left`. Adding the incoming occurrence from
`right` changes the bound to `fork`. The numbers below encode those two
labels for display. [Example][example]

```lean
import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example.Defs

open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example

#eval bounds.map (fun (left, across) => (number left, number across))
-- some (2, 1)
```

The regression also checks a mixed ordinary and Φ list, an entry bound,
same-block cut order, and rejection of empty, malformed, out-of-bounds
and unreachable uses. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[legality]: sea-of-nodes-gcm-legality.md
[synthesis]: ../../sea-of-nodes-gcm-synthesized-dominator-tree.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LatePlacement/Defs.lean
[theorems]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LatePlacement/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LatePlacement/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LatePlacement/Regression.lean
