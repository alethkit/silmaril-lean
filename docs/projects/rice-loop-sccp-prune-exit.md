# Remove an infeasible loop backedge in typed MLIR CF

`Loop.SCCP.PruneExit.rewrite` runs the existing simultaneous SCCP solver on
the native `Loop.MLIR.CF.Program`. It succeeds when the fixed point marks
the exit and leaves feedback unmarked. An unseen guard marks neither
successor and is refused. A guard that can both continue and exit is
refused as well. A guard known to continue lies outside this exit-only
profile.

The native profile carries one fixed-width word. Its total primitives
are word constants, flag-free `addi` and `muli`, and unsigned comparison.
The target is the repository's typed pure MLIR CF evaluator. The pass
reuses its existing lowering and replaces the header's `condBr` with a
`br` using the exact false edge. All original producer bindings, labels,
block arguments and captured inputs retain their identities and ordering.
The guard and feedback producer bindings stay in the header. There is no
dead-producer elimination or effectful CFG rewrite in this pass.

The native occurrence numbering in SCCP remains entry 0, feedback 1,
exit 2. In the emitted terminator's successor order, the surviving false
edge moves from slot 1 of the conditional to slot 0 of the direct branch.
The entry edge stays at slot 0 of the preheader branch. The header now
has only the preheader predecessor, and the exit still has only the
header predecessor. The MLIR representation routes block argument
operands on the edge and stores no separate predecessor index or Phi
column to renumber.

`header_shape` states the one-edge syntax with the original result wire.
`no_backedge_arrival` excludes a native finite arrival through the
removed occurrence on covered inputs. `header_frame` checks the exact
exit label and block argument. `arrives_frame` proves the original and
pruned headers agree on every covered arrival. The existing `lower_entry_frame`
checks the entry latch value. The pure target extends each block's
received argument with the same captured input environment. There is no
mutable state in this profile. `run_eq` compares actual CFG observations
at every block budget, including budgets that stop before the exit block.
`denotePart_eq` relates the rewritten CFG's partial return to native
evaluation.

- [API and theorem statements](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/PruneExit/Thms.lean)
- [Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/PruneExit/Regression.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Example

#eval run exitFacts 3 5 4 2      -- some (some 10)
#eval run exitFacts 2 5 4 2      -- some none
#eval run varyingFacts 7 0 4 1   -- none
#eval run unseenFacts 3 5 4 1    -- none
#eval run continueFacts 4 0 4 0  -- none
```

The admitted input starts at 5 with limit 4. The header returns 10;
the deleted edge's operand would have been 7. The admitted run needs
three blocks of fuel. The varying input starts at 0, increments to 4,
and then exits, so pruning would discard a reachable successor. The
outer `none` denotes refusal. `some none` denotes an admitted CFG with
no return within the supplied block budget.

## Rice source

Click's *Combining Analyses, Combining Optimizations*, §3.6 Figure 3.7
(printed p. 26) gives cyclic reachability. §3.7 Figure 3.8 (p. 28)
uses the constant fact in the conditional reachability equations. This
pass consumes the combined solution at one emitted typed conditional.
[Rice dissertation](https://hdl.handle.net/1911/16807)
