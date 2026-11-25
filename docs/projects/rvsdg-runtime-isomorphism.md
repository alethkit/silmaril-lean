# Observational renumbering for RVSDG linking and invocation

This proof connects the [typed interprocedural renumbering](rvsdg-interprocedural-isomorphism.md)
with the [numbered linker and closure interpreter](rvsdg-module-linking.md).
It uses the λ, δ and ω interfaces of Reissmann, Meyer, Bahmann and
Själander, *RVSDG: An Intermediate Representation for Optimizing
Compilers*, arXiv:1912.05036v2, §§4.2.1, 4.2.2 and 4.2.4.
The PDF SHA-256 is `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

Related runtime tuples agree exactly on data, state and control at
their typed ports. Globals compare their unit/vertex IDs using a
supplied relation and recursively compare initialized values. A
closure has no separate numeric identity in this interpreter. Related
closures have related ordered captures and typed-isomorphic body
graphs. The primitive machine must preserve the relation. This
assumption matters because a primitive can inspect numeric IDs or
closure representations. The allocation premise relates the IDs that
the actual linker gives corresponding δ vertices.
[Definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Defs.lean)

The proof runs each numbered table with its real local computations.
An auxiliary table records success or exhaustion separately for each
vertex. Typed source addresses relate its operand reads, and induction
on earlier producers relates corresponding outputs. A completed
table then yields related ordered results. The initializer and body
proofs use this argument at each child region. The invocation proof
also inducts on call depth and on the remaining iterations of θ.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Thms.lean)

`linkGraph_related` and `linkTerm_related` preserve and reflect
successful linking in the existing λ/δ runtime. When matching graphs
contain φ, this linker rejects both. Recursive φ environments are
outside this theorem. `invoke_related` compares calls at the same
call-depth and per-θ bounds, including selected γ arms and finite
θ execution. `exportedCall_related` composes the actual linker with
invocation at the same typed export port. `wireImports_related` transports
ordered import wiring, including fan-out. `exportedCall_withImports_related`
consumes related results from linking a provider, wires the client's
imports, links the client, and invokes its export. It covers supplied
typed import wiring between translation units. Bound exhaustion leaves
divergence undecided.

The fixture swaps two independent global allocations and two independent
vertices inside a λ body. The exported wrapper captures and calls that
λ. The observed global number changes from 0 to 1. Both invocations
exhaust at depth one and return data 42 and state 51 at depth two.
A second fixture renumbers a θ body and verifies the same bound
exhaustion and carried-state return across two body activations.
A separate client imports the provider's exported wrapper, captures it
and calls it from its own export. This path exhausts at depth two and
returns data 42 and state 51 at depth three in both numberings.
[Fixture](../../tests/ssa/RVSDGRuntimeIsomorphism.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRuntimeIsomorphism.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Thms +Silmaril.SSA.RVSDG.Interprocedural.Isomorphism.Thms +Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Thms'
```
