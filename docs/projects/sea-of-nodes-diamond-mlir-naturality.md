# Signature change for scoped Sea of Nodes lowering

`Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms` connects the
source-native diamond institution to the isolated scoped MLIR profile at
`Type`. The signature functor sends each primitive to its generated RVSDG
primitive profile. It lifts a relabelling through `Diamond.Opcode.pure` and
fixes `Diamond.Opcode.dispatch`. The state alphabet is `PEmpty` throughout.
Composition with #3162's scoped signature functor keeps every ordered
operand, result, region parameter, and yield profile.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Institution/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/MLIR/Institution/Thms.lean)

`rvsdg_lower_map` compares native relabelling followed by lowering with
lowering followed by relabelling the numbered RVSDG graph. The proof recurses
over the producer table and checks both γ arm terms. `lower_map` and
`translate_map` use the scoped RVSDG law to obtain equality on actual MLIR
terms and equations. `sentenceTranslation` is the natural transformation
between the existing institutions' sentence functors along
`signatureFunctor`.

The existing model constructor induces a scoped model from a native
diamond model. `model_reduct` proves that inducing a source reduct is the
same as reducing the induced scoped model. `inducedModels` is natural in
the two contravariant model functors, with its components going **from
source models to scoped models**. For each such source model,
`satisfaction_induced` is #3215's pointwise law applied to a native
institution sentence. Both natural transformations use the repository's
sentence and model functors.
[Institution variance](../../Silmaril/Logic/Institution/Morphism.lean) ·
[Scoped RVSDG laws](../../Silmaril/SSA/RVSDG/MLIR/Graph/Thms.lean)

## Model boundary

An arbitrary scoped model chooses its carriers and supplies total functions
for scoped symbols. The typed profile constrains those functions' arguments
and results. In particular it permits a γ interpretation that always calls
the first arm. To read native primitives from scoped operations by reusing
their carriers, the predicate carrier must agree with the native
`ULift Bool`. With compatible carriers a native primitive can be read from
result zero of `rvsdg.simple` for that primitive. The satisfaction theorem
also uses the induced dispatch and γ interpretations.

One check retains the induced carriers and all simple operations, replaces
γ with first-arm selection, and observes a different result at selector 1.
The no-reduct counterexample uses an unrestricted scoped model whose
carriers are all singletons. The two source diamonds use only Boolean
inputs and differ in what they return on the false branch. Their translated
equation holds in the singleton model, while the native equation fails in
every source model. Thus the translation cannot have a satisfaction-preserving
reduct on every scoped model at its image signatures. The public contract
is the commuting laws and satisfaction in induced models.

The regression composes identification of two typed arithmetic opcodes
with a swap. It checks equality of the composite and sequential sentence
translations, the reverse order of model reducts, and satisfaction after
translation. It also checks both model boundary examples.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/MLIR/Institution/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.MLIR.Institution.Regression'
SILMARIL_REPLAY_MODULE=Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Institution.Thms \
  lake env lean tools/compiler-explorer/Replay.lean
```

The source institution comes from #3237 at `f7cbd597e`. The scoped
satisfaction comparison comes from #3215 at `6ecc83d62`, and the scoped
signature and model laws come from #3162 at `4720c4a7a`.
[#3237](https://github.com/hiloopai/silmaril-lean/pull/3237) ·
[#3215](https://github.com/hiloopai/silmaril-lean/pull/3215) ·
[#3162](https://github.com/hiloopai/silmaril-lean/pull/3162)
