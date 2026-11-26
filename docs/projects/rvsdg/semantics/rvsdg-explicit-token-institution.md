# Equations on checked explicit-token RVSDGs

The institution's sentences are pairs of typed numbered graphs with the
same entry and exit interfaces. Both graphs must have
[`ExplicitRuntime.Checked`](../../../../Silmaril/SSA/RVSDG/NestedTheta/ExplicitRuntime/Defs.lean)
witnesses. Data ports are values or selectors. A final runtime port at
each boundary carries the single live token. Each binding takes its
designated live token, γ supplies it to the selected arm, and θ uses the
returned body token for its next activation or for its exit. This
admission predicate covers arbitrary nesting of the supported primitives,
γ and θ. An otherwise typed edge that returns an earlier token fails
admission.

The signature category and models are those of the
[partial ordered institution](rvsdg-nested-partial-institution.md)
over a fixed value alphabet and store type. Signatures distinguish total
pure primitives from partial `StateT σ Part` actions. Migrations preserve
ordered ports and primitive kind. Effect maps are injective at each
typed signature because block diagnostics observe the opcode. The
sentence map relabels the actual numbered graph and transports the
admission witness. Its identity and composition laws hold on the
numbered syntax. The model reduct precomposes primitive actions.

For every input tuple with its token, satisfaction compares:

- The typed result data and exact final token. The output tuple with its
  token is determined by these fields.
- Finite blocks with their typed opcode and input data, static child
  path and vertex position, and exact token on the attempted edge.
- The existence of productive divergence.

[Wire endpoint adequacy](rvsdg-nested-partial-wires.md) identifies each
of these observations with its ordered reading. Erasure retains every
port and producer number and interprets the former token positions as
unit. Graph erasure commutes with migration, and model erasure commutes
with the reduct. The translated equation therefore holds in a target
model exactly when the original equation holds in its reduct. The
endpoint transport relabels only the block's opcode. Its typed data,
address and attempt token are unchanged.

An undefined primitive action is an atomic blocked attempt. A missing
finite return can also come from productive feedback, so a partial
result alone cannot classify the execution. The institution compares
the existence of a productive run. Its scope is deterministic ordered
state with one physical token. Multiple token interfaces, arbitrary
premonoidal effects, diagnostic transport under renumbering, comparison
of infinite traces and a LambdaSSA sentence injection are outside this
milestone.

The fixture migrates an effect used under γ and θ. Two restarts advance
tokens 2 → 5 → 8. The returning branch observes payload 3 and token 11,
while the blocked variant reports payload 2, token 8 and the migrated
opcode at the same site. The continuing variant refutes its equation
with the blocked variant. A bypass retains the initial token. A
separate typed graph returning the stale entry token has no admission
witness and cannot form a sentence.

[Institution API](../../../../Silmaril/SSA/RVSDG/NestedTheta/Institution/Wires/Thms.lean) ·
[Fixture](../../../../tests/ssa/RVSDGNestedThetaPartialWires.lean)

## Reproduce

```sh
make check CHECK_TARGETS=+Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Thms
lake env leanchecker Silmaril.SSA.RVSDG.NestedTheta.Institution.Wires.Thms
```

## Sources

- Nico Reissmann, Jan Christian Meyer, Helge Bahmann and Magnus Själander,
  *RVSDG: An Intermediate Representation for Optimizing Compilers* (2020),
  arXiv:1912.05036v2, §§4.1.2–4.1.3, Definitions 1–3. PDF SHA-256
  `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
  [Versioned PDF](https://arxiv.org/pdf/1912.05036v2)
- Joseph A. Goguen and Rod M. Burstall, *Institutions: Abstract Model Theory
  for Specification and Programming* (1992), §2.1 Definition 1. PDF SHA-256
  `f6715ca333dd03dc153a65907c1c974fa151690bb94eafffc065c363265b634d`.
  [PDF](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf) ·
  [DOI](https://doi.org/10.1145/147508.147524)
