# Infinite execution of linked RVSDG tail calls

This slice extends the [finite recursive runtime](rvsdg-phi-calls.md)
and its [observational renumbering](rvsdg-runtime-isomorphism.md). It
uses the selected regions of γ and the recursion arguments of φ
from Reissmann, Meyer, Bahmann and Själander, *RVSDG: An Intermediate
Representation for Optimizing Compilers*, arXiv:1912.05036v2,
§§4.1.2 and 4.2.3. The PDF SHA-256 is
`861fb183f8b642327f3231a823bc0d2df7ebff17b39cd10ab7a2cc3a2be4f6a3`.
[Paper](https://arxiv.org/abs/1912.05036v2) · [PDF](https://arxiv.org/pdf/1912.05036v2)

A machine state contains the actual runtime callable and its typed
argument tuple. Inspection resolves the callable through the existing
closure or φ member environment. A zero-vertex region reads its result
wires. A one-vertex region forwards all outputs of its vertex in port
order. The machine executes a sole primitive, enters the selected γ
arm, or exposes a tail application as the next activation. A step
records one actual tail call. The syntax checks for this shape use
classical equality on types and wires.
[Transition definitions](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Defs.lean)

`Diverges` is an infinite stream of steps. A return and an unsupported
body have distinct outcomes, and both stop the machine. Unsupported
means the body is outside this slice. The full evaluator can still
return on such a body. The proof covers fixed φ member slots and
whole-tuple tail forwarding through selected γ arms. θ restarts,
general multiple-vertex regions, and continuations after a call are
outside the transition rules.

`step_invoke` relates each step to one activation in the actual bounded
interpreter at every remaining call and θ budget. `trace_returns_iff`
preserves and reflects the independent `Returns` judgment along any
finite step prefix. A productive infinite trace excludes all finite
`Returns` derivations by this correspondence.
[Evaluator correspondence](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Thms.lean)

The observational theorem transports a given stream in either
direction, matching its actual steps at the same indices and keeping
callables and arguments related. The result for linked exports uses
typed endpoint isomorphism, the recursive linker theorem, and the
explicit relation on global allocation IDs.
[Transport theorems](../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Tail/Thms.lean)

The regression links a self-recursive φ and an independent δ at two
different ω numberings. One γ arm calls the same linked member and
gives a constant stream with a checked self-transition. The other
arm returns data 7 and state 11. A separate two-vertex call illustrates
the unsupported outcome and returns in the full evaluator.
[Regression](../../tests/ssa/RVSDGRecursiveTail.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveTail.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```
