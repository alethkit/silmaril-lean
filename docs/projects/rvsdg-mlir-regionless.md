# RVSDG value graphs and regionless MLIR equations

The bridge in `Silmaril.SSA.RVSDG.MLIR.Regionless` uses the canonical equations
and models of both institutions.
[RVSDG](../../Silmaril/SSA/RVSDG/Institution/Thms.lean) ·
[MLIR](../../Silmaril/SSA/MLIR/Institution/Thms.lean) ·
[Bridge definitions](../../Silmaril/SSA/RVSDG/MLIR/Regionless/Defs.lean) ·
[Bridge theorems](../../Silmaril/SSA/RVSDG/MLIR/Regionless/Thms.lean)

## Boundary and translation

A `ProfileMap` maps the RVSDG value sorts to MLIR sorts and supplies a
regionless symbol for each opcode in the selected RVSDG dialect. The symbol
profile must match every operand and result position after the sort map. The
selected dialect's opcodes and the graph's external boundary use only value
ports. A first γ vertex would need a control input, which cannot come from a
value argument or an earlier value result.

`translateGraph` uses the numbered RVSDG evaluator with terms as values. It
starts with MLIR variables for the argument slots. Each primitive result
substitutes the terms at the operand wires into the corresponding result
projection of the regionless operation. The returned tuple follows the graph's
result wires, which can repeat or reorder producer outputs and omit unused outputs. An MLIR term
can duplicate a subexpression from a shared graph producer.

`ValueEquation.toRVSDG` packages the original numbered graphs as an RVSDG
equation, and `translateEquation` produces a regionless MLIR equation with
the same ordered boundary. `ProfileMap.pullback` interprets each primitive by
the matched MLIR symbol and uses the MLIR carriers at the mapped sorts.

## Guarantees

- `denote_translateGraph` gives equality at every input assignment and result
  slot. The observation is the returned value tuple in total deterministic
  models.
- `satisfaction` proves that the translated equation holds in an MLIR model
  iff the original RVSDG equation holds in its pullback.
- `translateGraph_precomp`, `translateEquation_precomp` and
  `ProfileMap.pullback_precomp` commute with RVSDG opcode relabelling and
  reduct.
- `translateGraph_map`, `translateEquation_map` and
  `ProfileMap.pullback_map` commute with MLIR signature change and model
  reduct, including sort reindexing.

The bridge's public contract is these graph, sentence and model laws for
matched profiles.

## Reproduce the checks

Run the bounded check and the regression from the repository root with its
pinned Lean toolchain. [Multi-result regression](../../tests/ssa/RVSDGRegionless.lean)

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.MLIR.Regionless.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRegionless.lean
```
