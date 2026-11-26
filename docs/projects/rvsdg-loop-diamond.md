# A flat LambdaSSA diamond with a loop on each arm

The admitted source is one flat LambdaSSA `Region.cfg`. Its entry
runs a typed classifier and enters one of two disjoint block tables.
Each arm is an existing acyclic-body θ fragment, with its own header,
body and feedback decision. Both exits of either arm carry a value of
type `M` and are redirected to one shared continuation. The continuation
is another admitted acyclic-body θ fragment with two external labels
carrying types `E` and `D`. The three acyclic bodies may contain
sequences and nested choices.

The classifier returns `(M + M) + Y`. The two inner injections both
select the left arm, carrying an `M` into it. The outer right injection
selects the right arm with its possibly different entry type `Y`. This
shares the existing typed carrier and connector operations. The source
entry implements the two cases with actual LambdaSSA case and branch
syntax. [Flat fork definitions](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/Sequential/Flat/Fork/Defs.lean)

The numbered target has a classifier, a binary γ, and one shared θ
at its outer level. The classifier gives γ a `Fin 2` selector, the
original sum carrier and the post-classifier token. The selector is
the bounded index of the outer sum injection, so each input has a typed
child region. Each child contains its own θ and a structural connector
which routes the returned payload into the continuation's input
carrier. Only the selected child receives the token. The common θ
reads both ports of the γ result. The checked splice computes this
numbered wiring with the same typed token discipline used within
each loop.

`LoopDiamond.Source` describes the admitted flat syntax.
`LoopDiamond.lower` constructs the dependent graph fibre
with a `LoopDiamond.Related` witness. `Related.typing` and
`Related.checked` provide the actual source typing and graph admission.
The constructors are indexed by the generated syntax and numbered wiring.
[Translation API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/LoopDiamond/Defs.lean)

## Semantics

`Flat.denote_fork` compares the relocated block table with the selected
arm's actual `Region.denote`. Elgot uniformity embeds each arm's
dispatcher into the disjoint union, keeping local feedback within that
arm. `Flat.denote_link` then factors the shared continuation as a
Kleisli bind. In coherent `StateT σ Part` instruction models,
`Related.region_returns_iff` preserves and reflects the external
label, its typed payload and the exact final token.
`Related.region_undefined_iff` compares the absence of finite
returns. The comparison admits partial operations and uses source-order
sequencing throughout. The partial observation identifies blocking and
infinite iteration.

The theorem covers the generated diamond family. Unrestricted reducible
CFG structuring and loop bodies containing additional θ are separate
developments.
[Observation theorems](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/LoopDiamond/Thms.lean)

The regression checks the actual producer addresses at the join. Both
arms take feedback, with different payload types and noncommuting state
updates. With initial token 1, the left arm hands token 17 to the shared
continuation, which exits at label 0 with payload 18 and token 24.
The right arm hands token 78 to the continuation, which exits at label 1
with payload `(3, 78)` and token 96. A second right-arm input takes
feedback indefinitely, by an invariant on every finite run derivation
that rules out a return. No fuel bound is used.
[Lean regression](../../tests/ssa/RVSDGLambdaSSALoopDiamond.lean)

## Recover the flat CFG from the graph

`LoopDiamond.Reverse.recover` takes the typed numbered graph and
returns an optional pair of the recovered flat LambdaSSA region and
its `LoopDiamond.Related` witness. The type indices give the entry,
handoff and exit sorts. The parser reads the classifier opcode, the
two ordered γ children and the common θ. It uses the serial recognizer
to locate the θ inside each arm and read its local labels, with an
independent size bound for each loop body. The right arm keeps its own
entry sort `Y`, while the left arm and shared tail enter at `M`.

The candidate is only a parse. Certification reconstructs the numbered
graph and checks recursive equality of opcodes, port sorts and wire
origins. This includes the classifier's selector wire and both producer
addresses feeding the shared θ. A well-typed regression retains the γ
payload edge but changes the shared θ's token source to the entry token.
It produces the same candidate as the original and fails certification.

`recover_isSome_iff` characterizes acceptance as literal equality with
an emitted graph. It covers all body associations and nested acyclic
choices in the three loops. Right-associated sources round trip to the
same flat region by `recover_generated`. Other associations may recover
a right-associated source with the same graph. The theorem concerns
the emitted numbering and layout. Arbitrary renumberings and arbitrary
CFG structuring are outside this recognizer's scope.

The recovered relation witness transports the existing observation
theorems to the actual `Region.denote` of the recovered CFG. The fixture
checks both typed exits and their tokens, and absence of a finite return
from the repeatedly restarting arm.
[Reverse API](../../Silmaril/SSA/RVSDG/LambdaSSA/Acyclic/Theta/LoopDiamond/Reverse/Thms.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Thms
lake env leanchecker Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Jad Ghalayini and Neel Krishnaswami, *The Denotational Semantics of SSA*
  (2024), arXiv:2411.09347v1, §§3 and 5.3. PDF SHA-256
  `5194f35c8375fc1c2ffd88d62bdf1c19d961894d1cc518ad68b5bb673b4f4114`.
  [Versioned PDF](https://arxiv.org/pdf/2411.09347v1)
