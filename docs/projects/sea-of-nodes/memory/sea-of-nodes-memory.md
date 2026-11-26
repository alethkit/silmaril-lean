# Sea of Nodes straight-line memory

[The memory fragment](../../../../Silmaril/SSA/SeaOfNodes/Memory/Defs.lean) models a
single ordered table of Loads and Stores ending in Return. Start provides
memory version zero. A Store takes the current version and produces the next.
A Load depends on a version and produces a scalar. Multiple Loads can
read the same version. Return consumes the latest version and its scalar
operand. The table fixes the order of effects, including a Load before an
overwriting Store.

Each memory input names Start or the Store that produced its memory. A
`MemoryInput` witness admits precisely the current producer. Scalar wires
reuse RVSDG's typed `Origin`, `Tuple`, and `Locals`. RVSDG's ordered
runtime similarly checks a live origin, with an output runtime slot on every
operation. Here a Load has only a scalar output. The operational rules resolve
memory edges against a table of logical snapshots. The denotation threads
only the current heap. `Graph.returns_iff_denote` proves agreement on both
the returned word and the final heap.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Thms.lean) ·
[Ordered runtime](../../../../Silmaril/SSA/RVSDG/OrderedRuntime/Structured/Defs.lean)

The profile uses already allocated, initialized cells indexed by `Fin cells`,
each holding one `BitVec 64`. Store reuses Mathlib's functional update. Equal
addresses refer to the same cell, and distinct addresses name disjoint cells.
Access is total on these typed addresses. Allocation, pointer validity,
byte overlap, exceptions, and alias-based rewrites are outside the profile.
The logical snapshots describe values on edges, and the proof fixes the
effect order of the table.

IR ’95 §2.5 and Figure 6 show a whole STORE value: LOAD consumes it and
STORE publishes a new one. The paper makes the STORE optional at exit.
Simple chapter 10 uses one memory chain and attaches its current version to
Return to retain stores. This profile exposes the final heap as part of the
observation. Its Point regression starts after allocation and initialization.
It stores to two fields and reads the first through the second Store's
memory edge. Further checks cover coincident addresses, a Load before an
overwriting Store, and rejection of a stale memory input.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 at `f0a6c675`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#one-memory-value) ·
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Regression
```
