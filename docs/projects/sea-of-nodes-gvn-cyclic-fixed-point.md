# Fixed-point structural GVN for one Sea of Nodes loop

`Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint` iterates the existing
synchronous refinement round. `run` checks stability before each
splitting round and stops on acceptance or when it runs out of fuel.
`normalize` starts from the typed profile seed with one round of fuel
per vertex. The keys and their occurrence order come from the one-round
model, including distinct argument positions and separate entry and
backedge positions for Phis.
[Definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/FixedPoint/Defs.lean) ·
[One-round model](sea-of-nodes-gvn-cyclic.md)

## Certified bound and fixed point

- `refine_no_merges` and `run_no_merges` preserve every existing
  separation, even with insufficient fuel. `classCount` counts the
  distinct labels used by vertices. `classCount_lt_refine` proves strict
  growth whenever a round starts from an unstable partition. The map
  from new classes to old classes is surjective and identifies the two
  new classes at a split, so the old partition has strictly fewer classes.
- `run_stable_of_fuel` shows that for any starting partition `p` on
  `n` vertices, `n - classCount p` rounds suffice. Every unstable
  round consumes one unit of fuel and raises the class count, which
  is bounded by `n`. A run at zero fuel simply returns its current
  partition. The bound implies stability even if the budget is consumed.
- `normalize_stable` proves that the default run reaches a stable
  refinement of the seed. `normalize_fixed` says an additional round
  leaves the same pairs together. This fixed-point statement allows
  the numeric labels to change.
- `normalize_coarsest` says every stable refinement of the typed seed
  also refines the result. A pair grouped by any such partition has the
  same profile and agrees on that partition's operand labels in order.
  As long as that partition refines the current one, the two keys still
  agree after those labels are mapped to the current partition. Induction
  over the rounds preserves the pair. Together with stability and seed
  refinement, this makes the result unique up to the same-class relation.

[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/FixedPoint/Thms.lean)

## Regression and scope

The fixture has two pairs of Phis that read each other on feedback.
Only one Phi reads a different entry argument. A one-round budget
splits that Phi but leaves its feedback user in the original class.
Two rounds separate the user as well, taking the class count from one
to two to three. Normalization keeps the two Phis of the uniform cycle together. The same fixed point with reversed
numeric labels passes the checker and the driver returns those labels
unchanged. A direct refinement round is free to renumber them.
[Lean regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/FixedPoint/Regression.lean)

The result is the coarsest **structurally** stable refinement for this
typed producer graph. Producer replacement and deletion are outside
the implementation. Semantic preservation requires an execution
correspondence with an entry relation and a per-activation simulation
for latch values, control choice, and exit observations. The iteration
performs synchronous scans and makes no worklist complexity claim.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Correctness
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Regression
```

## Source

Clifford Noel Click Jr., *Combining Analyses, Combining Optimizations*,
Rice PhD dissertation, February 1995, §§4.1–4.2, especially pp. 38–41. The typed
seed and refinement use the opcode split and the class of the
*i*th input. The dissertation propagates splits with Hopcroft's
smaller-partition worklist. Here each round recomputes the ordered
keys over the finite vertex list, and the strict class-count bound
certifies termination. The Rice PDF has SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice record](https://hdl.handle.net/1911/16807) ·
[Rice PDF](https://repository.rice.edu/server/api/core/bitstreams/c5ea1ab7-e6c6-41e7-8e06-3cd5b80aeccd/content)
