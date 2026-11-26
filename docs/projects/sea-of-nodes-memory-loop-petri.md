# Coloured Petri completion for the Sea of Nodes memory loop

This uses the existing nested RVSDG coloured firing model on the numbered
memory θ. Its places hold typed argument and output colours, and its
`Fire` relation updates the pending, waiting, and done markings. The
heap colour is the whole `Fin cells → BitVec 64` state value. The model
uses that type directly, with no enumeration of heap values or translation
to an ordinary uncoloured place/transition net.
[Firing model](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Defs.lean) ·
[Memory θ](sea-of-nodes-memory-loop-theta.md)

The θ owns one active child. Restart discards the completed child marking
and seeds a fresh one with the outgoing carried tuple, including its one
heap port. A read retains its colour, so previous heap snapshots can
remain in places until the marking is discarded. The heap chain gives
each primitive one designated incoming heap producer and routes its
outgoing heap to the next primitive. That includes the tail test after the
last effect. The next vertex cannot fire while that colour is absent.
Every reachable activation marking has a done prefix, and each firing
extends the prefix by one. Completion checks that all vertices are done
before θ can exit or restart. These are the guarantees for the logical
heap chain and for the ordered effects in each completed activation.
[Ordering certificate and statements](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Petri/Thms.lean)

`Graph.lowerTheta_finishes_iff` extends the pure loop's finite-completion
comparison. It identifies source returns with genuine finite firing
sequences that reach a completed marking with the same word and entire
heap. `Graph.activation_finishes_iff` exposes the corresponding one-body
boundary with its tag and heap. The fixture covers the effectful
zero-backedge case, two backedges, and the distinct heap observed by the
second activation. The statement concerns finite completion. Fairness
and maximal schedules are outside its scope.
[Pure loop completion](../../Silmaril/SSA/SeaOfNodes/Loop/Theta/Thms.lean) ·
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Petri/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Order
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Completion
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Petri.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Petri.Regression
```
