# A conditional theta in a flat LambdaSSA CFG

The admitted source is one actual flat LambdaSSA `Region.cfg`. Its entry
uses a typed classifier of result type `(E ⊕ D) ⊕ L`. The outer left choice
branches directly to one of the two actual external labels with payload
type `E` or `D`. The outer right choice enters the existing acyclic-body
loop at its typed header with payload type `L`. Header, body and join
form the existing flat block table. Feedback stays inside that table and
the classifier is executed once at entry. [Typed source](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Conditional/Defs.lean)

The forward fibre uses the existing classifier, forward γ and admitted θ
emitters. The classifier produces a selector and the existing loop carrier.
The bypass γ arm forwards the completed carrier. The other arm runs the
existing checked θ term on the active carrier. The γ continuation reads
both the result payload and the live token from the selected arm.
[Forward lowering](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Conditional/Defs.lean)

The reverse fibre requires a supplied parse of the actual numbered decoder.
The parse sees a classifier followed by a binary γ with an empty bypass arm
and a checked loop parse in the other arm. The existing loop decoder
recovers the typed blocks from the recorded labels. A full wiring certificate
checks the edges, including the classifier-to-γ input and γ-to-return result.
The reverse compiler then constructs the typed flat CFG from the decoded
instructions. This interface assumes a supplied parse and wiring witness.
[Reverse recovery](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Conditional/Reverse/Thms.lean)

The reusable entry lemma compares two actual `Region.denote` calls with the
same local dispatcher. The typed entry sends either an external result or
an input to the loop's header. Block actions use only their local payload,
so the dispatcher is independent of the retained entry environment. The
comparison uses the repository's coherent monadic Elgot interface.
[Entry factorization](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Thms.lean)

For every forward or reverse witness in coherent `StateT σ Part` models, the
explicit graph and actual SSA region agree on finite returned label, typed
payload and exact final token, and agree on absence of a finite observation.
The checked-wire bridge transports the same
result to the erased ordered graph. The SSA observation here is a partial
return. Block and productive-divergence diagnostics have a graph-side
meaning and remain outside the SSA comparison.
[Observation laws](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Conditional/Thms.lean) · [Checked-wire bridge](rvsdg-nested-partial-wires.md)

The regression adds two to the token in the gate before the loop header
doubles it. The loop feeds back once and its body reads the changed token.
The successful branch returns payload `(2, 22)` at the second label with
token `27`. A direct bypass returns at the first label with token `3`.
An undefined gate has no finite return. The stale-value variant keeps its
checked token wiring and the same labels but reads the old classifier
carrier instead of the γ result. The reverse witness rejects it.
[Fixture](../../tests/ssa/RVSDGLambdaSSAConditionalTheta.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3 and 6.1. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA* (2024),
  arXiv:2411.09347v1, §§3, 5.1 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
