# Portable finite observations of the Sea of Nodes memory loop

One native `Memory.Loop.Graph` supplies the same scalar inputs and initial
heap to all three backends. `Portable.Observation` certifies an exact return
word and the entire final heap. Its fields expose the λSSA typing and
finite evaluation, the counted λSSA continuation, the numbered θ bounds,
and coloured Petri completion of that same numbered graph.
[Native loop](https://github.com/hiloopai/silmaril-lean/pull/3318) ·
[λSSA](https://github.com/hiloopai/silmaril-lean/pull/3386) ·
[Numbered θ](https://github.com/hiloopai/silmaril-lean/pull/3353) ·
[Coloured Petri](https://github.com/hiloopai/silmaril-lean/pull/3368)

`backedges` is the number of completed source backedges. The numbered
evaluator returns `none` at that bound and the encoded result at
`backedges + 1`, since the exit activation also runs the body.
The Petri field asks for a finite completion. The scope is the native
ordered tail-tested profile with one carried whole heap and invariant
scalar inputs.

## Lean API

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms

open Silmaril.SSA.SeaOfNodes.Memory (Heap Val ValueSort Word encodeInput encodeResult)
open Silmaril.SSA.SeaOfNodes.Memory.Loop
open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)

example {args : List ValueSort} {cells : Nat}
    (g : Graph args) (input : Tuple (Val cells) args) (initial final : Heap cells)
    (backedges : Nat) (word : Word) (returned : g.ReturnsAfter input initial backedges word final) :
    Portable.Observation g input initial backedges word final :=
  (g.returnsAfter_iff_portable input initial backedges word final).mp returned

example {args : List ValueSort} {cells : Nat}
    (g : Graph args) (input : Tuple (Val cells) args) (initial final : Heap cells)
    (word : Word) (completed : Finishes (thetaRuntime cells) g.lowerTheta
      (encodeInput initial input) (encodeResult word final)) :
    ∃ backedges, Portable.Observation g input initial backedges word final :=
  (g.returns_iff_portable input initial word final).mp
    ((g.lowerTheta_finishes_iff input initial word final).mpr completed)
```

The regression uses the same graph for an immediate effectful exit and
a two-backedge return. All three backends observe each case's exact
heap. The numbered checks use bounds (0,1) and (2,3), respectively.

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Portable.Regression'
```
