# RVSDG

Start with the [RVSDG overview](overview.md) for the typed graph and term
representations, their operational semantics, liveness, and the coloured firing
model.

## Semantics and institutions

- [The Cartesian RVSDG equation institution](semantics/rvsdg-categorical-institution.md)
- [Categorical denotations for RVSDG primitives and γ](semantics/rvsdg-categorical.md)
- [Equations on checked explicit-token RVSDGs](semantics/rvsdg-explicit-token-institution.md)
- [The RVSDG dialect institution](semantics/rvsdg-institution.md)
- [Renumbering nested RVSDG regions](semantics/rvsdg-nested-isomorphism.md)
- [The ordered-state institution for nested RVSDG](semantics/rvsdg-nested-ordered-institution.md)
- [Observing partial primitives in nested RVSDG](semantics/rvsdg-nested-partial-institution.md)
- [Partial observations of nested explicit RVSDG wires](semantics/rvsdg-nested-partial-wires.md)
- [Renumbering live nested RVSDG firings](semantics/rvsdg-nested-petri-isomorphism.md)
- [Coloured firing for compositional θ](semantics/rvsdg-nested-petri.md)
- [Stateless equations for nested RVSDG](semantics/rvsdg-nested-stateless-institution.md)
- [Compositional θ regions](semantics/rvsdg-nested-theta.md)
- [Ordered RVSDG chains with a single runtime wire](semantics/rvsdg-ordered-runtime.md)
- [Lifting the ordered RVSDG runtime model](semantics/rvsdg-structured-runtime-lift.md)
- [Whole-region θ with ordered runtime effects](semantics/rvsdg-structured-runtime-theta.md)
- [Structured RVSDG with one ordered runtime](semantics/rvsdg-structured-runtime.md)
- [Categorical whole-region θ](semantics/rvsdg-theta-categorical.md)
- [The deterministic RVSDG θ institution](semantics/rvsdg-theta-institution.md)
- [Tail-controlled θ in the RVSDG](semantics/rvsdg-theta.md)

## LambdaSSA correspondence

- [Typed λSSA ↔ RVSDG correspondence](lambdassa/rvsdg-lambdassa.md)
- [Recovering LambdaSSA from a numbered acyclic-body θ graph](lambdassa/rvsdg-lambdassa-acyclic-raise.md)
- [A typed θ wrapper for acyclic LambdaSSA bodies](lambdassa/rvsdg-lambdassa-acyclic-theta.md)
- [A physical runtime token for θ with an acyclic LambdaSSA body](lambdassa/rvsdg-lambdassa-acyclic-token.md)
- [Compositional lowering for typed acyclic LambdaSSA bodies](lambdassa/rvsdg-lambdassa-acyclic.md)
- [A conditional theta in a flat LambdaSSA CFG](lambdassa/rvsdg-lambdassa-conditional-theta.md)
- [Physical runtime wires for the typed LambdaSSA diamond loop](lambdassa/rvsdg-lambdassa-diamond-explicit-runtime.md)
- [A typed diamond inside a two-exit LambdaSSA loop](lambdassa/rvsdg-lambdassa-diamond.md)
- [Linking flat LambdaSSA fragments at a typed exit](lambdassa/rvsdg-lambdassa-flat-link.md)
- [Linear LambdaSSA loops with explicit runtime wires](lambdassa/rvsdg-lambdassa-linear-chain.md)
- [Ordered loop translation between LambdaSSA and RVSDG](lambdassa/rvsdg-lambdassa-ordered-theta.md)
- [Sequential θ in the shared LambdaSSA categorical denotation](lambdassa/rvsdg-lambdassa-sequential-freyd.md)
- [Recovering a flat LambdaSSA CFG from two numbered θ loops](lambdassa/rvsdg-lambdassa-sequential-raise.md)
- [Two successive θ loops from a flat LambdaSSA CFG](lambdassa/rvsdg-lambdassa-sequential-theta.md)
- [Single-exit λSSA region correspondence with RVSDG](lambdassa/rvsdg-lambdassa-single-exit.md)
- [Translating one-block LambdaSSA loops to RVSDG θ](lambdassa/rvsdg-lambdassa-theta.md)
- [A typed three-block LambdaSSA loop with explicit runtime wires](lambdassa/rvsdg-lambdassa-three-block.md)
- [An ordered two-block LambdaSSA loop](lambdassa/rvsdg-lambdassa-two-block.md)
- [Two typed external exits in a LambdaSSA/RVSDG loop](lambdassa/rvsdg-lambdassa-two-exit.md)

## MLIR bridges

- [Scoped MLIR-style lowering for stateless RVSDG feedback](mlir/rvsdg-mlir-feedback.md)
- [Scoped MLIR for acyclic RVSDG](mlir/rvsdg-mlir-graph.md)
- [RVSDG value graphs and regionless MLIR equations](mlir/rvsdg-mlir-regionless.md)

## Interprocedural graphs and runtime linking

- [Interprocedural RVSDG interfaces](interprocedural/rvsdg-interprocedural.md)
- [Linking and invoking RVSDG modules](interprocedural/rvsdg-module-linking.md)
- [RVSDG φ linking and finite recursive calls](interprocedural/rvsdg-phi-calls.md)
- [Infinite execution of linked RVSDG tail calls](interprocedural/rvsdg-recursive-tail.md)
- [Observational renumbering for RVSDG linking and invocation](interprocedural/rvsdg-runtime-isomorphism.md)
- [Typed renumbering of RVSDG translation units](../rvsdg-interprocedural-isomorphism.md)

## Graph composition and recognition

- [Recognizing the typed cut in a numbered RVSDG](composition/rvsdg-numbered-cut-recognition.md)
- [Splicing numbered RVSDG components with explicit state](composition/rvsdg-numbered-splice.md)
- [Serial cuts between checked RVSDG and flat LambdaSSA regions](composition/rvsdg-serial-cuts.md)
- [Recognizing numbered serial RVSDG graphs](composition/rvsdg-serial-recognition.md)

See also the [SSA guide](../ssa.md) and [Sea of Nodes guides](../sea-of-nodes/README.md).
