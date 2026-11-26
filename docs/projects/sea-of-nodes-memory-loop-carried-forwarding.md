# Forward a Load through a memory loop backedge

Simple chapter 10 pushes a Load of a memory Φ onto the incoming edges.
For a loop it checks that the backedge Load folds against a matching
Store. This increment implements that case for the first Load of a
native tail-tested `Memory.Loop.Graph`, with one captured address and
ordered, initialized word cells. The incoming memory follows IR ’95’s
STORE dependencies and Region/Phi convention.
[Pinned Simple `LoadNode.idealize`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/LoadNode.java#L64-L88) ·
[IR ’95 §§2.5, 3.1–3.2](https://doi.org/10.1145/202530.202534)

`Carried.rewrite` uses the existing exact exit check to require that the
final Store targets the first Load’s original address argument. The Store
must take the same word wire as the body Return, so the existing test word
also supplies the scalar Φ on feedback. The first Load sees version zero.
Earlier Stores keep their order. The final Store determines the carried
cell even if one of those earlier Stores aliases it. A subsequent Store
would supersede the checked witness. The captured arguments are fixed
throughout the run, so the check requires no address inequality facts.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Defs.lean) ·
[Exact exit check](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Thms.lean)

The target’s entry table performs one Load and exports it with the
initial heap. The target body is the original typed suffix
`Memory.Body args [[.word]] 0`, whose first local is now the scalar Φ
operand. Each taken backedge supplies the last stored word and whole
updated heap. `seed_agrees` establishes the cached-cell invariant at
entry. `rewrite_step_agrees` reestablishes it on feedback, including
agreement of the projected memory transition and of any exit result.
The exact-backedge and finite-return theorems quantify over every typed
input, initial heap, and entire final heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Thms.lean)

The fixture logs the initial value 7 and the carried values 1 and 2 on
successive activations. It also exits at zero backedges with the entry
value logged and all Stores executed. An extra same-address Store of
the old value fails the exit check and would break the feedback
invariant. This profile uses the same scalar wire for feedback and the
tail test. It leaves separate feedback and test exports, writes after
the selected Store, and changing addresses for further extensions.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Forwarding/Carried/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression
```
