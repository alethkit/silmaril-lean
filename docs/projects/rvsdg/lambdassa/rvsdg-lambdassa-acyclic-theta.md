# A typed θ wrapper for acyclic LambdaSSA bodies

The [acyclic body grammar](rvsdg-lambdassa-acyclic.md) supplies the
single-entry, single-join body. The wrapper adds two typed instructions.
The header returns either the first external exit or a body parameter.
The join returns either the second external exit or a new header
parameter. The entry jumps to the header.

The source is one flat LambdaSSA CFG. Local labels 0 and 1 are the header
and join. The body compiler's local labels stay in order and shift by two.
The body compiler's original external join becomes local label 1. The
relocation preserves the type of every edge and the only edge back to
the header comes from the join's feedback case. The external labels
carry the two exit payload types independently.
[Typed CFG](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Defs.lean)

The numbered RVSDG term has one θ. Its header γ selects either the
direct exit or the compiled acyclic body, including any of its nested
γ regions. The join executes once after the body and emits the exit or
feedback tag. The θ carrier represents the two exit payload types and
the active header payload by a sum. The direct header exit only repacks
its payload.
[Numbered θ lowering](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Lowering/Defs.lean)

The proof uses the repo's strong Elgot Freyd semantics with the
central-unit and region-typing coherence hypotheses of the
[fixed diamond](rvsdg-lambdassa-diamond.md). In the inner dispatcher,
the join's back edge completes the current activation. Elgot fixpoint
supplies the forward equations for the actual typed body blocks.
The arbitrary-join continuation theorem for the acyclic compiler then
folds those equations into the structured body followed by the join.
The existing codiagonal and pure-uniformity result groups the flat
dispatcher and restricts its feedback to the header payload. Primitives
are sequenced using composition and may be noncentral. The theorem is
for this single-loop shape with a generated acyclic body.
[Denotation equality](../../../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Categorical/Thms.lean)

The fixture checks an asymmetric seven-block CFG. Starting at `2` takes
the nested choice, produces the join payload `(2, 41)`, and feeds back
`1`. The next activation takes the other outer arm and exits through the
join with `(1, 102)`. Starting at `0` takes the separate header exit
with `7`. The fixture uses the numbered term's deterministic evaluator
for these finite runs and checks the model-polymorphic equality at the
same typed CFG.
[Lean fixture](../../../../tests/ssa/RVSDGLambdaSSAAcyclicTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Lowering.Defs
lake env leanchecker Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Fold
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
