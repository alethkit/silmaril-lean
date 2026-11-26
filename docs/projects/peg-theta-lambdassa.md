# Checked ordered PEG loops to λSSA

The adapter lowers the ordered single-loop PEG bundle from
[#4012](https://github.com/hiloopai/silmaril-lean/pull/4012) through its
existing numbered RVSDG θ graph. It emits the existing one-block Isotope
λSSA CFG. The entry jumps to local label zero with the packed input, and
a successful continue activation jumps back to that same label with the
next packet. The stop arm branches to label one inside the CFG, which
leaves at external exit zero. The header receives one block parameter
with a product field for each carried port in order.
[Existing λSSA loop form](../../Silmaril/SSA/RVSDG/LambdaSSA/Theta/Defs.lean) ·
[Adapter definitions](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Defs.lean)

The λSSA dialect instruction contains the actual numbered acyclic RVSDG
body and executes one activation with `Graph.run`. Its result is a sum
of the packed exit and feedback payloads. The RVSDG selector zero maps to
the exit injection, and one maps to the feedback injection. The λSSA CFG
performs all restarts. Its target instruction keeps the body in RVSDG
form, so this translation is at the loop boundary. A per-vertex λSSA
translation of the body would require separate wiring, γ and instruction
lowering proofs.
[Numbered-body adapter](../../Silmaril/SSA/RVSDG/LambdaSSA/Theta/Operational/Defs.lean)

The operational bridge compares actual `LambdaSSA.Semantics.Region.Eval`
and `Follow` with numbered θ `Returns`. The forward proof uses finite
CFG derivations and deterministic block observations. The reverse proof
builds one CFG follow step per θ activation. Each primitive returns the
ordered packet with unchanged ambient state. `lower_hasType` checks the
input, header packet and sole result type. `lower_eval_iff` composes the
operational theorem with the checked PEG tuple bridge, proving exact
agreement of finite evaluations at external exit zero with fully defined
Figure 11 tuples. `firstExit_of_eval` recovers the shared PEG pass count
and all defined eval prefixes.
[Operational θ adapter theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Theta/Operational/Thms.lean) ·
[PEG correspondence](../../Silmaril/SSA/PEG/Bridge/Theta/Region/LambdaSSA/Thms.lean)

The PEG theorem assumes the checked parentless single-loop boundary, pure
total primitives, and Boolean negation for the certified PEG exit opcode.
The typed packet runner charges one unit per header visit, including the
stopping visit. Successful fuel corresponds to finite execution. An
exhausted bound gives no termination classification. The theorems cover
finite successful execution. Partial primitives, failure and trap
observations, divergence equivalence, and general CFG lowering are outside
this result.

## Checks

```sh
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/PEGStructuredTheta.lean
for module in \
  Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Defs \
  Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Theta.Operational.Correctness \
  Silmaril.SSA.RVSDG.LambdaSSA.Theta.Operational.Thms \
  Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Defs \
  Silmaril.Proofs.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Correctness \
  Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Thms tests.ssa.PEGStructuredTheta; do
  SILMARIL_REPLAY_MODULE="$module" LEAN_NUM_THREADS=1 \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
done
```

The three-slot fixture exercises the actual header backedge and the ordered
return `(0, 11, 12)` after two simultaneous updates from `(2, 10, 1)`.
It also checks an already-false guard, which enters the header once and
exits without a backedge. The bounded runner distinguishes two units of
fuel from the three needed for the first input.
[Regression](../../tests/ssa/PEGStructuredTheta.lean)
