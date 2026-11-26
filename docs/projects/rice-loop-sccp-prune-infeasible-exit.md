# Prune an infeasible exit from typed MLIR CF

`Loop.SCCP.PruneInfeasibleExit.rewrite` takes a pure
`Loop.MLIR.CF.Bank.Program` and input facts. It admits the rewrite when
the existing simultaneous SCCP solution marks the backedge and leaves the
exit unmarked. The emitted header's conditional becomes a direct branch
to the original header label with the entire original feedback operand
column. Every operand reads the same old activation. This pass and
[backedge removal](rice-loop-sccp-prune-exit.md) share the branch selector
and its checked operand-routing laws.

The native entry, backedge, and exit occurrence numbers remain 0, 1, and
2. The retained target successor stays at terminator slot 0. The typed
target stores arguments on edges and uses no separate predecessor index.
The entry block, producer bindings, labels, and the now-unreachable
exit block remain in the output. The profile carries an ordered bank of
fixed-width words, has one returned word, and uses the pure project MLIR
CF evaluator.

`header_shape` gives the direct branch and its exact operand list.
`header_frame` and `arrives_frame` give exact successor-frame agreement,
including the simultaneous feedback payload. On covered inputs,
`run_eq` gives equality for every target block budget and `runs_none`
shows that both CFGs exhaust every budget. `no_finite_return` excludes a
finite native return, and `denotePart_eq` and `denotePart_eq_none` identify
the partial observations. `rewrite_eq_none_iff` describes refusal.
[Public API](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/PruneInfeasibleExit/Thms.lean) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/PruneInfeasibleExit/Regression.lean)

## Example

```lean
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneInfeasibleExit.Example

#eval route 1 300 4              -- some (4, 302, 2)
#eval route 4 302 2              -- some (2, 304, 5)
#eval run (.constant 0) 8 0      -- some none
#eval run (.constant 1) 3 1      -- none
#eval run .overdefined 8 0       -- none
#eval run .bottom 8 0            -- none
#eval refusesVarying             -- true
```

The bank has widths `i8, i16, i8`. The next bank is
`(old.b, old.payload + 2, old.a + 1)`, so using the freshly written
first field would give the wrong third field on the first step.
`route` evaluates the pruned CFG header. `some none` denotes admission
followed by target budget exhaustion. The outer `none` denotes refusal.
The varying case uses the earlier two-field counter that eventually exits.

## Rice source

Click's *Combining Analyses, Combining Optimizations*, §3.6 Figure 3.7
(printed p. 26) gives cyclic reachability, and §3.7 Figure 3.8 (p. 28)
connects conditional reachability to the propagated constant.
§3.8.1 discusses using the combined solution in transformation. This
slice consumes that solution at one emitted pure-loop conditional.
[Rice dissertation](https://hdl.handle.net/1911/16807)
