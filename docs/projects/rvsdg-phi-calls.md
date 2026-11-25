# RVSDG φ linking and finite recursive calls

The φ implementation follows Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers*,
arXiv:1912.05036v2, §4.2.3 and Definitions 7–8 for φ, and §4.3 for θ. The versioned PDF has
SHA-256 `861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

The ω linker reads typed imports and produces the ordered export tuple.
It links λ closures and δ initializers as before. At φ, it reads the
outer context once and packages the static member table with the context.
Each output contains that group environment and a typed member index.
The stored environment does not contain its own member references.
Invocation reconstructs the region's recursion arguments and its
in-scope earlier physical λ outputs as references to the same group.
It then reads the selected λ's captures and enters the body with the
ordinary argument tuple. Module linking traverses the same typed graph
or term interfaces used for λ, δ, φ and ω. `link_toGraph` proves exact
agreement on exports, including member references and numbered global
identities.
[Runtime definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Defs.lean) ·
[Recursive linker](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Defs.lean)

The inductive `Returns` judgment has explicit premises for entering a
callable, running its body, applying a callable, entering the chosen γ
arm, and completing θ iterations. A stopping body publishes the carried
tuple. A continuing body feeds that tuple to a fresh activation with
an empty local prefix. Both body execution and recursive calls use the
same judgment. Its rules are independent of the bounded evaluator.
`call_iff` proves that a call returns an exact typed value/state tuple
iff some pair of call-depth and per-θ bounds returns it.
`returns_eventually` supplies sufficient bounds valid at every larger
pair. During a single θ invocation the remaining iteration count
decreases, while its body and callees still receive the full per-θ
budget. Exhaustion at a particular bound leaves divergence undecided.
The linker takes a supplied import tuple. External import cycles and
linking by symbol name are outside this slice.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Thms.lean)

The first fixture links two mutually recursive members. The first
captures the second through a recursion argument, and the second
captures the first through its earlier physical λ output. Both capture
an imported value, pass a decreasing state through alternating calls,
and return the captured value and final state at zero. A second linked
φ member enters θ and calls itself inside the selected γ arm of the
body. The fixture checks exhaustion independently at each bound and
the exact returned tuple when both bounds suffice.
[Fixtures](../../tests/ssa/RVSDGPhiCalls.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPhiCalls.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```
