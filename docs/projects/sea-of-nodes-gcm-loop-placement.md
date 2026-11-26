# Choosing a loop-aware GCM placement

Click's PLDI ’95 schedule-early and schedule-late passes constrain placement
by the operands and uses. Section 2.4 favors the lowest dominator-tree
position in the shallowest loop nest. This slice applies that ranking to
the existing finite enumeration of typed CFG cuts for one pure total
floating value. [PLDI ’95 §§2.2–2.4][paper] · [Archived PDF][pdf] ·
[Cut discovery][discovery]

## Inputs and ordering

The caller supplies the typed CFG's finite block inventory, a sound
dominator certificate, the operand and use sites, and a loop-depth function
from block IDs to natural numbers. `acceptedCuts` filters `candidateCuts`
through the existing checker. Both exact successor occurrence and argument
number are checked for each Phi use, which is read at the predecessor's
terminator cut. [Placement checker][checker] · [Definitions][defs]

`chooseLoopPlacement` minimizes the supplied loop-depth labels. Among cuts
at the minimum depth it selects the greatest length of the supplied
dominator address. Equal scores keep the first cut in enumeration order.
The entry precedes the supplied labels, and within each block the cuts
are ordered from zero through the terminator cut. [Cut enumeration][discovery] ·
[Definitions][defs]

The caller supplies the depth labels and is responsible for their
loop analysis. The minimality theorem concerns those labels and the
accepted cuts in the finite inventory. Computing or validating loop nests
and moving instructions are outside this slice.

## Guarantees

- `chooseLoopPlacement_sound` places every result in the actual cut
  enumeration and proves `Legal` using the existing checker.
- `chooseLoopPlacement_minimal` compares the chosen scores with every
  checker-accepted cut in the enumeration. The supplied loop depth is
  minimal. At that depth the supplied address length is maximal.
- `chooseLoopPlacement_eq_none_iff` preserves the failure condition of
  unranked discovery. With complete reachability and dominance evidence,
  `chooseLoopPlacement_complete` excludes every legal cut in the
  represented blocks when the result is empty. [Theorem header][thms]

## Regression

The typed CFG has a preheader, a header with a self-backedge, and an exit
that receives a Phi operand over the header's other conditional edge.
The fixture assigns loop depth one to the self-loop header and zero
elsewhere. Its complete dominator certificate accounts for the backedge
by induction on structural paths.

The inventory puts the exit and header before the preheader. With the
operand available after the preheader's binding, unranked discovery
picks the header. Ranking picks the shallower preheader. The exit would
win on the dominator-address tie-break if the read were at the exit.
The Phi use is on the incoming edge and forbids that candidate. A second
request checks both the deeper-address preference and enumeration order
within a block. [Regression][regression]

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopPlacement.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopPlacement.Regression
```

[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopPlacement/Defs.lean
[thms]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopPlacement/Thms.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopPlacement/Regression.lean
[discovery]: sea-of-nodes-gcm-discovery.md
[checker]: sea-of-nodes-gcm-legality.md
[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
