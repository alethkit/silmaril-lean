# Typed λSSA from a pruned quad loop

`Quads.Loop.Blocks.Prune.LambdaSSA.lower` feeds the source-derived
pruning result directly to the generic λSSA emitter. If pruning succeeds,
the entry and feedback occurrences pack the retained fields in source
order, and the header unpacks precisely that carried signature. The
original function inputs remain available in the captured environment.
This composes the two-block profile of Cliff Click's *From Quads to
Graphs*, §3.1 and §4.1, with the existing λSSA packing and typing.
[Pruning](sea-of-nodes-quad-loop-phi-pruning.md) ·
[Generic emitter](../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Thms.lean) ·
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

`lower_hasType` checks the emitted region, and `lower_eval_iff` relates
all finite λSSA observations to source returns, including the packed
value at external exit zero and the unchanged ambient state.
`Generic.Fuel.run` executes the emitted λSSA terms, case and branches.
For an accepted program, source budget `b` agrees exactly with CFG
fuel `b + 1` by `run_succ`, including exhaustion. Each local block visit
costs one unit, including the visit that returns. The preheader and
external exit consume no fuel. The executable runner uses decidable
equality on primitive sort tags and accepts flat entries and blocks.
[Composition theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/LambdaSSA/Thms.lean) ·
[Runner](../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Fuel/Defs.lean)

The regression inspects the emitted header syntax and counts three
carried fields where the full-bank emission packs six. The shared source
takes two backedges and returns `29`. The emitted CFG exhausts fuel zero
through two and returns `29` at fuel three. The zero-backedge input
returns `12` at fuel one.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/LambdaSSA/Regression.lean)

Save this fixture to a Lean file and run it with `lake env lean <file>`.

```lean
module

meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA (lower)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel (run)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)

private meta def observed (fuel : Nat) : Option Nat := do
  let code ← lower program
  match ← run arithmetic (inputEnv arithmetic (input 3)) fuel code with
  | (0, .pair (.atom ⟨(), n⟩) .unit) => some n
  | _ => none

#eval [0, 1, 2, 3].map observed  -- [none, none, none, some 29]
```

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Prune.LambdaSSA.Thms
```
