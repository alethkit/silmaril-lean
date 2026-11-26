# Discovering a legal cut for one floating value

Click’s *Global Code Motion/Global Value Numbering* uses operand definitions
to constrain schedule early (§2.2), and use sites to constrain schedule late
(§2.3). A Phi input is used on its corresponding predecessor edge. The
placement checker expresses those dominance constraints and compares cuts for
sites in the same block. This discovery pass searches the cuts in a finite
block inventory and returns the first accepted cut for one pure total
floating value. [PLDI ’95 proceedings][paper] · [Archived PDF][pdf] ·
[Placement checker][checker]

## Search and guarantees

A typed `Cfg` supplies each labelled block's body by lookup. The caller
supplies the finite list of typed labels to search. The enumeration always
includes the anonymous entry first, then the listed blocks in order. In each
block it visits cut zero through the terminator cut in increasing order.
The cut counts already completed bindings. At that cut an insertion would run
after those bindings and before the next instruction or terminator reads.
`mem_candidateCuts` characterizes this enumeration exactly.
[Definitions][defs] · [Theorems][thms]

The request supplies operand availability sites, use sites, and a sound
`DominatorTree`. It needs no placement witness. Each Phi use gives the source
block, the exact terminator occurrence, and the successor argument index.
The checker validates the occurrence and index before using the source
terminator cut. Two arms to the same target are checked as separate uses.
`discoverPlacement_sound` proves that a returned cut passes the checker,
which establishes `Legal` by `checkPlacement_sound`. [Checker contract][checker]

`discoverPlacement_eq_none_iff` says failure excludes every checker-accepted
cut in the enumeration. A sound tree may leave reachable blocks unmarked or
omit dominance facts. When its reachability mask and ancestry test also have
the converses in `DominatorTree.Complete`,
`discoverPlacement_eq_none_iff_no_legal` says failure excludes every
`Legal` cut in the represented blocks. Covering all reachable blocks extends
that claim to the whole CFG. [Theorems][thms]

The chosen position is determined by enumeration order. The loop-depth
heuristic in §2.4, construction of the dominator tree and the def-use request,
transport through block arguments, and execution equivalence after motion
are outside this slice.

## Regression

A middle block with two bindings has a conditional whose two occurrences
pass different operands to one join. An operand available after binding one
and an ordinary use before binding two force cut one. The search moves past
the entry and the join to select that cut. Making the operand available only
after binding two leaves no legal represented cut. The fixture also checks
both Phi resolutions, the absent jump slot, and an out-of-range argument.
[Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.Discovery.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.Discovery.Regression
```

The archived PLDI PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[checker]: sea-of-nodes-gcm-legality.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/Discovery/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/Discovery/Thms.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/Discovery/Regression.lean
