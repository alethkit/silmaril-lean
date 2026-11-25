# RVSDG φ linking and finite recursive calls

The φ implementation follows Reissmann, Meyer, Bahmann and Själander,
*RVSDG: An Intermediate Representation for Optimizing Compilers*,
arXiv:1912.05036v2, §4.2.3 and Definitions 7–8. The versioned PDF has
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
callable, running its body, applying a callable and entering the chosen
γ arm. It never invokes the bounded evaluator. `call_iff` proves that a
call returns an exact typed tuple of values and states iff there is a
call-depth bound at which the evaluator returns that tuple.
`returns_eventually` provides a sufficient depth for all larger bounds.
The adequacy result uses θ budget zero. Selected paths may execute
primitives, calls and γ arms. An executed θ is outside this relation,
while θ code in an unselected arm is allowed. Bound exhaustion by itself
does not decide divergence. The linker takes an already supplied import
tuple. Cycles across external modules and linking by symbol name are
outside this slice.
[Public theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Thms.lean)

The fixture links two mutually recursive members. The first captures
the second through a recursion argument, and the second captures the
first through its earlier physical λ output. Both capture an imported
value, pass a decreasing state through alternating calls, and return
the captured value and final state at zero. It checks the exact exports
of both linkers, bounded failure, successful results from both members
and the corresponding independent finite derivation.
[Fixture](../../tests/ssa/RVSDGPhiCalls.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGPhiCalls.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```
