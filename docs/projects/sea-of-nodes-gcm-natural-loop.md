# Checked natural-loop depth for GCM placement

Click's PLDI ’95 §2.1 computes loop nesting information before placement.
Section 2.4 uses that information to favor a shallow loop nest and then
a low dominator-tree position. This slice computes the depth contribution
of one supplied natural-loop backedge on the typed CFG used by cut
discovery. It passes that score to the existing cut selector.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [Cut discovery][discovery] ·
[Placement ranking][ranking]

## Admitted CFG and path model

The caller supplies the finite block inventory, a sound dominator
certificate, and a descriptor naming the typed header, latch, and exact
latch successor slot. The inventory includes the anonymous entry and
must contain only reachable blocks and be closed under every actual
successor occurrence. The descriptor must name an actual latch-to-header
edge, and the certificate must show that the header dominates the latch.
Branches are structural edges, including both slots of a conditional.
[Definitions][defs]

The member set consists of the header and all reachable blocks with a
finite path to the latch in the graph with the header omitted. The
executable traversal starts at the latch and repeatedly adds predecessors
from the finite inventory, stopping at the header. It consumes a
remaining candidate each time it adds one. A self-backedge has only the
header as a member. This is the usual predecessor-closure construction,
restricted to the entry-reachable CFG. [Natural loops][natural] ·
[Definitions][defs]

## Guarantees and scope

- `mem_vertices_iff_reachable` proves that the checked inventory is exactly
  the entry-reachable CFG. `checkBackedge_sound` certifies the successor
  occurrence and dominance.
- `checkedMembers_iff` identifies the computed set with the path model.
  `depth_eq_one_iff` identifies the members with score one. All other
  blocks have score zero.
- `choosePlacement_sound` and `choosePlacement_minimal` establish legality
  and minimum derived depth over checker-admitted cuts. Among equal
  scores the existing ranking favors longer dominator addresses, then
  keeps the first enumerated cut. With a valid loop descriptor and
  complete dominator evidence, `choosePlacement_complete` excludes every
  represented legal cut on failure. [Theorem header][thms]

The score is total loop nesting depth in the single-loop profile. On a
CFG with other loops it measures only the supplied backedge's natural
loop. Backedge discovery, coalescing several latches, a loop nesting
tree, and code motion are outside this slice.

The regression discovers an internal body block, includes the header and
latch, and excludes the preheader and exit. Unranked discovery first
finds the latch cut for an exit-edge Phi use, and the derived score
selects the preheader cut instead. Invalid cases include a real
non-dominating edge, absent and wrong-target successor slots, and an
incomplete inventory. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.NaturalLoop.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.NaturalLoop.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/NaturalLoop/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/NaturalLoop/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/NaturalLoop/Regression.lean
[discovery]: sea-of-nodes-gcm-discovery.md
[ranking]: sea-of-nodes-gcm-loop-placement.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[natural]: https://www.cs.cornell.edu/courses/cs6120/2020fa/lesson/5/#natural-loops
