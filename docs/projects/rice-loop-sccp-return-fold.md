# Folding a constant return in a native loop

`Loop.SCCP.ReturnFold.rewrite` reads the return fact from the simultaneous
loop SCCP solution. For a constant, it appends a typed nullary literal to
the existing header table and redirects the return to the new producer.
The preheader stays in place. The original guard and feedback wires are
embedded in the larger scope using the existing GVN weakening operation.
The caller supplies `Literals`, a literal encoder in the graph’s opcode
signature with a proof of its interpretation in the analysis model.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/ReturnFold/Defs.lean) ·
[Loop SCCP](rice-loop-sccp.md)

`rewrite_ok_iff` identifies the exact accepted result. `rewrite_error_iff`
distinguishes an unseen return (optimistic bottom) from an overdefined
return (top in the implementation’s order). Both produce a refusal.
`guard_eq` preserves the guard read on every activation. The structural
proof keeps the same feedback tuple and changes only the value on an
exit. At a covered concrete input, the native SCCP return theorem
identifies that value with the literal. `evalBackedges_eq` gives equality
at every native backedge budget. `returns_iff` and `noFiniteReturn_iff`
give the corresponding finite return and divergence guarantees.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/ReturnFold/Thms.lean)

The fixture extends the existing eight-bit loop’s opcode profile with a
literal. With increment zero and an unclassified external flag, every
finite return is zero. The rewritten result uses producer 2 and the
guard still reads producer 1. A false flag exits immediately. A true
flag takes the backedge forever, which the regression proves for the
same accepted rewrite. Increment one with a true flag widens the
return fact. Increment zero with a known true flag leaves the return
unseen.

```lean
module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example.Defs

open Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Example

#eval resultProducer 0 .overdefined            -- Except.ok (some 2)
#eval run 0 .overdefined false 0                 -- Except.ok (some 0)
#eval run 0 .overdefined true 12                 -- Except.ok none
#eval resultProducer 1 (.constant ⟨true⟩)       -- Except.error Refusal.overdefined
#eval resultProducer 0 (.constant ⟨true⟩)       -- Except.error Refusal.unseen
```

The rewrite covers a single return of a total pure native loop in the
supplied model and for inputs covered by the entry facts. It retains
the producer table and adds one literal. Dead producer elimination,
guard folding, and general CFG rewriting are separate. The Rice
dissertation describes using constants after analysis in §3.8 and the
opening of Chapter 4.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Loop/SCCP/ReturnFold/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Loop.SCCP.ReturnFold.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```
