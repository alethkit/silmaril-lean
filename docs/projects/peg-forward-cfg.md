# PEG to λRTL and a forward flat CFG

`ForwardCFG.toLambdaRTL` consumes the numbered RVSDG graph produced by the
[checked PEG bridge](peg-ir-bridge.md). It uses `Graph.toTerm` to linearize
the actual graph, then emits the existing `LambdaRTL.Region`. Argument
slots and producer vertices have disjoint register names. Each producer
becomes one assignment to its numbered temporary. An assignment retains
the instruction and its typed operand and result profile. Each operand
reads its original wire, including repeated uses of a shared result.
The external return carries a right-nested tuple of the ordered root
wires, with unit at the end. Empty root tuples use unit alone.
[Definitions](../../Silmaril/SSA/PEG/Bridge/ForwardCFG/Defs.lean)

The generated symbol alphabet uses the copy, primitive and select symbols
from the RVSDG bridge. The source wires and profiles are intrinsically
typed. The existing λRTL syntax has an unindexed carrier, so the induced
`Option` model represents each atomic value with a sort tag. That model
uses decidable equality on the user data sorts to decode ordered operands.
The correctness proof shows that every decoded operand tuple in an
admitted run is well typed and every application succeeds. Use
`inputStore` to load the typed boundary, or supply any store satisfying
`Inputs`. The condition only constrains argument slots in that boundary.

## Observations proved

- `evalSSA_fromRVSDG` identifies the packed RVSDG result with the lexical
  reading of the generated λRTL region at the external label `()`.
- `evalRTL_fromRVSDG` identifies the payload for the mutable reading.
  It uses `Region.evalObs_eq_evalSSA` with a proved `NoClobber` witness.
  The full run has a final store. `Region.evalRTL_frame` gives equality with
  the initial store on every argument register and every temporary whose
  number is at least the number of vertices in the emitted RVSDG table.
- `toCFG` uses the repository's `CFG.flatten`. `cfg_run` composes with
  `CFG.run_flatten` to retain the packed payload and store frame at
  `Sum.inl ()`. `cfg_blocks` certifies that the generated CFG has just
  its entry body and the external return transfer.
- `observeCFG_peg` decodes the payload, keeps the exit, and forgets the final
  store. At each ordered root, wrapping the decoded value in `some`
  recovers the actual guarded Figure 11 observation. `observeCFG_mlir`
  gives equality with the assembled result slots of the checked regionless
  MLIR block in the induced model.
  [Theorem header](../../Silmaril/SSA/PEG/Bridge/ForwardCFG/Thms.lean) ·
  [λRTL agreement and frame](../../Silmaril/SSA/LambdaRTL/Thms.lean) ·
  [CFG flattening correctness](../../Silmaril/SSA/LambdaRTL/CFG/Thms.lean)

## Boundary and follow-ups

The fragment is pure, total, topologically numbered and loop-free. Its
φ nodes are value-selects. Both operands already have defined values,
so the emitted code needs no branch to evaluate the chosen arm. The
generated entry contains assignments and one external transfer. The
`Option` model can reject malformed inputs, and the preservation result
guarantees a successful return under `Inputs`.

The forward CFG semantics resolve jumps only in the remaining block
suffix. Multi-block adapters would have to pass live values explicitly,
check dominance or `NoClobber` at joins, and state which final registers
are observable. The existing lexical forward CFG agreement theorem
`runSSA_eq_obs_of_isSSA` and versioned CFG theorem `versioned_runSSA`
handle exit and payload under their respective dominance and model
hypotheses. This adapter uses the λRTL region lexical/overwriting
agreement directly. [Forward CFG agreement](https://github.com/hiloopai/silmaril-lean/pull/3221) ·
[Versioned CFG generation](https://github.com/hiloopai/silmaril-lean/pull/3250)

The separate typed Isotope λSSA–RVSDG bridge `raiseGraph` admits unary
instructions on a single typed variable and one result. A translation
through it would need typed products and new operand/root correspondence
for the multi-operand, multi-result graphs here. Machine RTL likewise
needs a word encoding, the `RootFits` fragment, and matching register
frame, memory and call oracle. λRTL's `Option` outcome here gives no
machine trap or divergence observation. Structured feedback requires a
separate proof of the iteration and exit polarity, the first true pass
in the defined prefix, and every prefix check for Figure 11 eval.
[Typed λSSA](rvsdg-lambdassa.md) ·
[Machine RTL adapter](../../Silmaril/Machine/OfLambdaSSA/Thms.lean) ·
[Ordered θ semantics](rvsdg-ordered-runtime-theta.md)

## Checks

```sh
make check CHECK_TARGETS='+Silmaril.SSA.PEG.Bridge.ForwardCFG.Thms PEGForwardCFGTests PEGIRBridgeTests PEGCoreTests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGForwardCFG.lean
for module in \\
  Silmaril.SSA.PEG.Bridge.ForwardCFG.Defs Silmaril.SSA.PEG.Bridge.ForwardCFG.Thms \\
  Silmaril.Proofs.SSA.PEG.Bridge.ForwardCFG.Correctness tests.ssa.PEGForwardCFG; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \\
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The fixture runs both φ choices, repeated operand and root wires,
ordered subtraction, an external return, a written temporary and
an untouched argument and temporary. It checks PEG and MLIR agreement
and rejection of a wrongly tagged argument. [Regression](../../tests/ssa/PEGForwardCFG.lean)
