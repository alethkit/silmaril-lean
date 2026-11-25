# Two successive θ loops from a flat LambdaSSA CFG

The source family uses one flat LambdaSSA `Region.cfg`. Each of its
two disjoint local block ranges is produced by the existing typed
acyclic-body loop compiler. The first loop has two exits with the same
payload type, and their branches both enter the second header. All
first-loop feedback remains in the first range. The second loop has no
edge back to the first, and its two external labels retain their
original, potentially different payload types.
[Flat syntax and typing](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Defs.lean)

The flat dispatcher follows the repository's chosen `Region.denote`.
Its local labels are a dependent sum partitioned into the two block
ranges. Uniformity compares each labelled phase to its original
single-loop CFG, and codiagonal separates internal feedback from the
one-way handoff. The resulting equation is a monadic bind of the actual
denotations of the two CFGs. It holds for the repository's lawful Elgot
monads with `RegionCoherent`.
[Flat denotation theorem](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Thms.lean)

The forward fibre contains a numbered graph with two θ vertices
and a typed link. Each θ reuses the admitted single-loop body,
including its nested γ arms. The link decodes either first-loop exit
and forwards the exact token. Its guard rejects a carrier still tagged
as feedback, which a returned first loop cannot produce. On its
domain the link performs only data routing and leaves the token intact.
The result is checked by the existing single-live-token discipline.
[Graph and forward relation](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Wires/Defs.lean)

Every relation witness preserves and reflects the actual second-loop
exit label, its typed payload, the final token, and the absence of a
finite return in coherent `StateT σ Part` models. The graph proof reuses
the two individual numbered-loop observation theorems. The second θ
is in the continuation of the first observation, so a first loop
without a finite return cannot supply its input. The observation
theorem describes finite returns and `Part.none`.
[Boundary theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Wires/Thms.lean)

The fixture takes a feedback edge in each loop. The second body reads
the length of the accumulated token and eventually returns `(3, 10)`
at its second exit with token `[1,2,3,1,2,3,4,5,6,4,5,6]`. With
input zero, every completed first-loop activation requests feedback
with zero. An induction on finite runs excludes a first return and
therefore excludes the handoff.
[Lean fixture](../../tests/ssa/RVSDGLambdaSSAAcyclicSequentialTheta.lean)

The source witness fixes the block layout and shared handoff payload.
The scope excludes general CFG conversion and reverse translation.

## Reproduce

```sh
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms'
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Thms
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
