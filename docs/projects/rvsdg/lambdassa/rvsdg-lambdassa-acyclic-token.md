# A physical runtime token for θ with an acyclic LambdaSSA body

The explicit compiler admits the whole generated single-θ shape from
the typed acyclic body grammar. Its numbered graph carries a real
runtime port. A primitive consumes the live token and yields its next
token. A γ passes the classifier's token into the selected child and
supplies that child's returned token to the continuation. Sequencing
uses that same rule recursively. The last body continuation is the
join instruction. Its token accompanies either the next θ activation
or the decoded typed exit. The direct header exit uses pure routing.
[Numbered compiler and admission](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/ExplicitRuntime/Defs.lean)

`elaborate` produces the numbered graph and a syntax-directed
`Related` witness indexed by the actual flat LambdaSSA region.
`Related.checked` admits that graph through the repository's existing
`EntryChecked` discipline. The physical token is distinct from the
implicit state used in the categorical interpretation. Both readings
use the same source instruction interpretations.
[Implicit-effect wrapper](rvsdg-lambdassa-acyclic-theta.md)

The acyclic proof works at an arbitrary typed continuation. It compares
the entire partial observation, including the result and token on
success, with ordered `StateT σ Part` sequencing. The θ proof uses the existing
iteration boundary lemma to compare the whole graph to the shared
activation loop. The categorical wrapper theorem and the repository's
Kleisli agreement identify that loop with actual LambdaSSA
`Region.denote` under `Agreement.RegionCoherent`.

`Related.region_observe` gives equality of the partial observations
after encoding the LambdaSSA exit and its final state as the graph's
result tuple. `Related.region_returns_iff` compares the finite return
at each decoded label, with its own payload type and the exact token.
`Related.region_undefined_iff` compares `Part.none` on the two sides.
The proof covers the generated single-loop shape with implicit
`StateT σ Part` computations on the source side.
[Boundary theorems](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/ExplicitRuntime/Thms.lean)

The asymmetric fixture takes the nested left arm and feeds back after
the join reads the accumulated token. The restarted header selects the
other outer arm and returns through the join with payload `(1, 14)`
and token `[1,2,3,4,6,1,2,5,6]`. Another input selects an undefined
inner instruction and has no finite observation. The direct header exit
also checks that it skips the body.
[Lean fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicToken.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Thms
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Body
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Graph
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Kleisli
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
