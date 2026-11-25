# Sequential θ in the shared LambdaSSA categorical denotation

The exact flat two-loop CFG denotes the categorical composite of the
first lowered θ, a pure payload handoff, and the second lowered θ. The
handoff folds the two first-loop labels, which both carry the second
header's payload type, and introduces its singleton value context. The
second loop keeps both typed external exits. The categorical result
uses the repository's actual `denoteRegion`.
[Lowering and factorization](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Categorical/Thms.lean)

The proof sends the internal labels to a value coproduct of the two
phase label contexts. Each typed relocation uses an equality transport
and a coproduct injection in the value category. The pure embedding
preserves these coproducts, and pure uniformity compares the actual
flat dispatcher to the relocated one. The reusable `iterate_phases`
lemma groups feedback local to each phase using naturality, pure
uniformity and codiagonal. Its first and second step arrows and its
handoff may be arbitrary computation arrows. Only the phase injections
used for uniformity must be pure.
[Phase factorization](../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Categorical/Phase.lean)

The CFG theorem uses the same strong Elgot Freyd structure and central
unit hypothesis as the single-loop theorem. Each generated block reads
only its own parameter. The dispatcher can discard the unused entry
context through the image of the cartesian projection, using the
existing payload-dispatch theorem. The handoff uses cartesian pairing
with the unique unit map, and its image is central. The block arrows
and both loop computations can be noncentral. All their sequencing
uses composition in source order. The proof uses no interchange of
computations.
[Flat dispatcher proof](../../Silmaril/Proofs/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Categorical/Dispatch.lean)

A supplied reverse decomposition determines the same categorical
composite for the recovered flat source. In the induced
`StateT σ Part` Kleisli model, the usual LambdaSSA coherence assumption
identifies the specialized arrow with `Region.denote` after decoding
the label. The existing explicit graph theorem then compares that
result to the graph observation, including the final token and
`Part.none`. Physical token ports belong to this specialization. The
abstract category sequences computations with implicit effects.
[Reverse and state theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Categorical/Wires/Thms.lean)

The checked fixture specializes the recovered graph to partial state
and compares feedback in both loops and the case with no first-loop
return. It also retains the malformed handoff rejection.
[Lean fixture](../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  §§4.1.2–4.1.3. Versioned PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [arXiv:1912.05036v2](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), §§5.1 and 5.3. Versioned PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [arXiv:2411.09347v1](https://arxiv.org/pdf/2411.09347v1)
