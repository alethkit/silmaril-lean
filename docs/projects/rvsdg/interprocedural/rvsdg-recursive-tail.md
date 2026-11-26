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
[Transition definitions](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Defs.lean)

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
[Evaluator correspondence](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Thms.lean)

The observational theorem transports a given stream in either
direction, matching its actual steps at the same indices and keeping
callables and arguments related. The result for linked exports uses
typed endpoint isomorphism, the recursive linker theorem, and the
explicit relation on global allocation IDs.
[Transport theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Tail/Thms.lean)

The regression links a self-recursive φ and an independent δ at two
different ω numberings. One γ arm calls the same linked member and
gives a constant stream with a checked self-transition. The other
arm returns data 7 and state 11. A separate two-vertex call illustrates
the unsupported outcome and returns in the full evaluator.
[Regression](../../../../tests/ssa/RVSDGRecursiveTail.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursiveTail.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Thms'
```

## Straight-line primitive prefixes

The prefix machine shares the same activation and outcome types. It
decodes the actual resolved graph and visits the bindings in its numbering.
Each total primitive reads its typed operands from the entry tuple and
the current locals, and appends one result tuple. This includes state
ports and supports independent bindings and repeated reads of a wire.
A region can return any well-typed result wiring after its primitives.
A final γ or application must forward its entire result tuple in order.
Only the selected γ arm is visited, with fresh locals. A call target
contains the new argument tuple, including any state, and begins its
own body on the next transition. θ, non-tail applications and non-tail
γ vertices remain unsupported.
[Prefix definitions](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Prefix/Defs.lean)

The separate `Executes` judgment derives local execution to a return
or a tail call. The inspector agrees in both directions on these
outcomes. The infinite trace theorem matches every edge with the
declarative call-entry rule and conversely. `step_invoke` uses exactly
one unit of the actual evaluator's call bound for the entire local
prefix. `trace_returns_iff` relates the independent finite return
judgment at either end of a finite path, including the full returned
tuple. An unsupported outcome has no enabled transition.
[Correspondence](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Tail/Prefix/Thms.lean)

The linked renumbering theorem uses the existing typed isomorphism,
recursive linker, and finite-return transport. It applies when no
reachable activation is unsupported under either numbering. The proof
constructs an infinite trace on the other side using actual outgoing
call steps. It makes no claim about matching the two traces at each
index. In particular, a valid topological renumbering can move an
unused primitive after a γ or a call, outside the recognized tail
shape. Unconditional inspection transport for multiple-vertex bodies
would need a recognizer and proof that handle such schedules.
φ member slots stay fixed.
[Linked productivity](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Tail/Prefix/Thms.lean)

For pointwise matching, the proof relates operands at the corresponding
terminal vertices before either vertex runs. The row-store simulation
compares the producers of each operand through the typed endpoint map.
This gives the same selector and related child arguments at a γ, and a
related callable and full argument tuple at an application. Primitive-only
regions return related tuples. The premises allow independent primitives
to exchange numbers before the terminal vertex. The runtime represents
primitive effects through wired values, including state, and the theorem
uses the existing `PrimitivesRespect` contract.

`step_match_right` and `step_match_left` require support on the receiving
side. The supplied transition establishes support at its own source.
`stream_match_right` and `stream_match_left` match a supplied productive
stream at every index, requiring support at the receiving side's reachable
entries. These premises concern the selected path, so an unselected arm
can contain unsupported control.
[Pointwise theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Isomorphism/Tail/Prefix/Thms.lean)

The linked recursive fixture increments a state wire before γ and
uses a child-local primitive result as an argument of the recursive
application. Each call in its infinite mode takes state `n` to
`n + 1`. Its terminating mode takes two transitions and returns data
7 and state 3, matching the real evaluator at call depth 3. The
fixture swaps the module's independent δ and φ vertices and also swaps
the state update and an independent data copy in the φ member body.
The matched linked streams carry exactly state `n` at index `n`. A non-tail call demonstrates the
unsupported outcome and still returns in the full evaluator.
[Prefix regression](../../../../tests/ssa/RVSDGRecursivePrimitivePrefix.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Thms
lake env lean -DautoImplicit=false -DwarningAsError=true tests/ssa/RVSDGRecursivePrimitivePrefix.lean
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Prefix.Thms +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Isomorphism.Tail.Thms'
```

## Correspondence with continuation microsteps

A tail activation corresponds to the actual continuation machine's
call job, with the same callable and full typed argument tuple. A
matching segment follows actual continuation steps to the first
successive call entry. It has at least one step, and every interior
state is outside a call entry. The proof follows the tail inspector's
declarative rules through primitive operands and the selected γ arm.

`ForwardedOver` records the actual saved inputs and locals in each
frame and the suffix that forwards the newest binding's entire tuple.
A segment can add these forwarding frames above the original stack.
Their unwinding preserves the full returned tuple. The converse
requires the source tail entry to be admitted, the source stack to
consist of forwarding frames above the empty stack, and the segment
to end at its first successive call. A returning activation unwinds
those frames without encountering another call.
[Segment definitions and theorems](../../../../Silmaril/SSA/RVSDG/Interprocedural/Runtime/Recursive/Continuation/TailCall/Thms.lean)

The stream proof locates every supplied tail activation at a strictly
increasing index of one productive continuation execution. It also
splits microsteps at supplied successive call boundaries. With the
same admission and frame premises, the split execution reflects a
tail stream. This correspondence concerns the primitive-prefix and
selected γ tail fragment. Non-tail continuations and θ executions
are outside the claim.

The linked φ regression computes two successive continuation
boundaries at microsteps `14` and `28`, with the original callable,
the exact state arguments `1` and `2`, and the saved γ and application
frames. It checks the productive stream and the reverse boundary
statement on that linked program.
[Regression](../../../../tests/ssa/RVSDGRecursivePrimitivePrefix.lean)

```sh
lake build --wfail +Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Thms
make check CHECK_TARGETS='+Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.TailCall.Thms'
```
