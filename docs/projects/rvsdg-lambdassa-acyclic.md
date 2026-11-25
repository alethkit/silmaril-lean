# Compositional lowering for typed acyclic LambdaSSA bodies

An admitted body has one typed entry payload and one typed join payload. Its
constructors are an instruction, sequencing at a common payload type, and a
binary choice. The classifier is a source instruction returning a sum. The
arms accept the corresponding summands, produce the same join type, and can
contain further choices and sequences. Every source block reads only its own
parameter.
[Typed grammar and LambdaSSA compiler](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Defs.lean)

The source compiler allocates the continuation before its predecessors. A
sequence uses the next body's entry as its join. Both arms of a choice get
the same join, with label offsets determined by their placement. Each
allocated block produces a real LambdaSSA branch or case with typed sites.
`Compiled.blockAt_forward` proves that every target number is greater than
its local block number. The top-level region has one external label carrying
the join payload.
[Forward-edge theorem](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Thms.lean)

The RVSDG compiler emits a numbered term with scoped γ children. A sequence
wires the first result into the next computation. A classifier emits a sum
and the matching `Fin 2` selector. Each γ arm starts with a pure unpack of the
matching summand, then executes its own translated subtree. The sum is
necessary because the numbered γ syntax gives both arms the same input port
signature. In the categorical interpretation of the admitted terms, a
coproduct injection represents the matched tag and payload together, so
copairing supplies the selected arm's typed input. Each effectful vertex
represents exactly one source instruction.
[Numbered γ compiler](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Lowering/Defs.lean)

The categorical proof uses the same strong Elgot Freyd assumptions as the
[fixed diamond](rvsdg-lambdassa-diamond.md). Elgot fixpoint gives the edge
equations for the actual finite-label dispatcher. The allocation proof folds
those equations by induction on the body, with an arbitrary interpretation
of the existing join. Copairing and composition preserve source order and
allow noncentral branch and continuation arrows. With the repository's
region typing coherence and central-unit hypotheses, `denoteRegion_join`
compares actual LambdaSSA `denoteRegion` and the admitted γ term followed by
any typed computation continuation. The proof applies to this acyclic
grammar and its generated terms.
[Categorical theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Categorical/Thms.lean)

The asymmetric fixture checks a six-block CFG where one arm of the outer
choice contains another choice and the three paths reconverge at one join
instruction. It checks the two levels of γ in the real term and specializes
the categorical equality at an arbitrary continuation.
[Lean fixture](../../tests/ssa/RVSDGLambdaSSAAcyclic.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms +Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Thms
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Dispatcher
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Fold
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  §4.1.2. Versioned PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [arXiv:1912.05036v2](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), §§5.1 and 5.3. Versioned PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [arXiv:2411.09347v1](https://arxiv.org/pdf/2411.09347v1)
