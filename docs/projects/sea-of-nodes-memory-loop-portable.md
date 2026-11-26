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

## Native equations and emitted programs

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
```

The native `Institution.inst` uses the memory diamond's typed entry
interfaces and models. A signature map sends each address or word port
to a port of the same sort. It renames the ordered body's entry uses
and the invariant stop port. Model reduct pulls back that valuation
and keeps the cell count. `Equation.satisfaction` gives the law for
these maps. At a model, an equation compares the partial returned word
and entire final heap at every initial heap.
[Native API](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Thms.lean)

`lambda_observation_iff` characterizes every finite execution of the
emitted, typed λSSA region. Its exit is zero, its payload is the packed
native word, and its final state is the same whole heap. The preservation
direction uses `Graph.returns_iff_portable`. `theta_observation` uses the
existing numbered RVSDG partial observation on `Graph.lowerTheta`,
with the original typed inputs and initial heap on the runtime wire.
The output is the native partial result encoded as the word/heap tuple.

`lambda_satisfaction` and `theta_satisfaction` preserve and reflect
native equations at the given valuation. The reindexing laws apply
to re-emission at mapped typed entry interfaces and the corresponding
model reducts. `lambda_no_return_iff` and `theta_no_return_iff` identify
absence of finite observations at an individual initial heap. The
comparison uses finite returns and the canonical initialized-cell
memory interpretation.
[Backend API](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Thms.lean) ·
[RVSDG partial observation API](../../Silmaril/SSA/RVSDG/NestedTheta/Partial/Thms.lean)

The equation regression compares two loops that load zero and return
zero after different stores. It checks the output heaps on both targets,
swaps the two address ports, and checks a fixed-backedge input with
empty finite observations.
[Equation regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Regression'
```
