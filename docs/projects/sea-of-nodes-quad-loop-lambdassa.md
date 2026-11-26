# From a two-block quad loop to typed λSSA

`Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.lower` passes the
graph constructed from the source preheader and header into the existing
generic λSSA loop emitter. The emitter schedules the producers as lets
and carries the complete typed register bank through one packed header
argument. This compositional step keeps the full-bank placement from
the source construction. Φ pruning remains open.
[Quad source construction](sea-of-nodes-quad-preheader-loop.md) ·
[Generic emitter](../../Silmaril/SSA/SeaOfNodes/Loop/LambdaSSA/Generic/Thms.lean)

The preheader jump and the conditional's feedback leaf are distinct
`PhiView.EdgeOcc` values for the same header label. `entry_branch` and
`feedback_branch` identify their argument terms as the actual computed
entry and feedback columns, including the case binder on the latter.
`entry_latch` and `feedback_latch` identify the packed values with the
corresponding source banks. This preserves the association between
operands and control occurrences from Cliff Click's *From Quads to Graphs*,
§3.1 and §4.1.
[1993 manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

`lower_hasType` checks the generated region. `lower_eval_iff` characterizes
every finite λSSA observation by a successful source budget, exit zero,
the packed typed returned value, and the unchanged state.
`returns_within_iff` relates budget success to a counted graph run.
The budget measures completed source backedges. The ordinary λSSA
evaluation judgment is unbounded.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/LambdaSSA/Thms.lean)

The fixture imports the same source program used by the preheader-loop
regression. With the counter set to three, budgets zero and one exhaust
and budget two returns `29`. The emitted region returns that value with
the two-backedge witness. With the counter set to one, budget zero
returns `12`, and the emitted region returns `12` as well.
[Shared source fixture](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Example/Defs.lean) ·
[Full regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Blocks/LambdaSSA/Regression.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Thms

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv instruction)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

example : program.evalBackedges arithmetic 1 (input 3) = none := rfl
example : program.evalBackedges arithmetic 2 (input 3) = some (29 : Nat) := rfl

example : Eval (instruction arithmetic) (inputEnv arithmetic (input 3)) (lower program)
    (42 : Nat) 0 (.pair (.atom ⟨(), (29 : Nat)⟩) .unit) 42 :=
  (returns_iff program arithmetic (input 3) 42 (29 : Nat)).mp ⟨2, rfl⟩
```

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Blocks.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.LambdaSSA.Thms
```
