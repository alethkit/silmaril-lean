# Logical Triton and Gluon tiles

This slice fixes shape `[64]` and element type `i32`. Expressions have one
available tile argument. Inputs to splats are already evaluated `i32` bit
patterns. A range is `[start, start + 64)` with `0 ≤ start < 2^31 - 64`, so
both endpoints fit in signed `i32` and the length is a power of two.
[Definitions](../../Silmaril/SSA/MLIR/Triton/Defs.lean)

| Layer | Operation | Admitted interpretation |
| --- | --- | --- |
| Triton IR (`tt`) | `tt.make_range` | The element at logical coordinate `i` is `start + i` as `i32`. |
| Triton IR (`tt`) | `tt.splat` | Repeat the scalar at every logical coordinate. |
| Gluon frontend | `gl.arange` | Create the same range in an explicitly laid-out tile. |
| Gluon frontend | `gl.full` | Splat the supplied `i32` value into an explicitly laid-out tile. |
| Gluon frontend / TritonGPU IR (`ttg`) | `gl.convert_layout` / `ttg.convert_layout` | Preserve shape, element type and the value at every logical coordinate while changing the slot assignment. The slice uses the default `assert_trivial=False`. |

The Gluon frontend uses the Triton range and splat operations with layout
encodings and emits `ttg.convert_layout` for explicit layout conversions.
`Gluon.Expr.erase` maps range and fill to the corresponding layout-free Triton
expressions and drops conversions. `Triton.Expr.toTensor` interprets those
expressions using the existing Tensor `denseConstant` and `splat` operations.
[Triton make range](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/include/triton/Dialect/Triton/IR/TritonOps.td#L854-L875) ·
[Triton splat](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/include/triton/Dialect/Triton/IR/TritonOps.td#L427-L439) ·
[Gluon frontend semantics](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/python/triton/experimental/gluon/language/_semantic.py#L210-L248) ·
[TritonGPU conversion](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/include/triton/Dialect/TritonGPU/IR/TritonGPUOps.td#L31-L44)

## Blocked layouts

Both layouts are rank-one `BlockedLayout([R], [32], [1], [0])` with an empty
`cga_layout`, one CTA and one 32-lane warp. At extent 64 there are two abstract
register slots per lane in either layout. For `R = 1`, the 32-element block is
tiled twice, so slot `(lane, reg)` maps to coordinate `lane + 32 * reg`.
For `R = 2`, the block covers the shape exactly and the coordinate is
`2 * lane + reg`. `Layout.slotToIndex_indexToSlot` and
`Layout.indexToSlot_slotToIndex` prove that each assignment is a bijection.
[Gluon layout tutorial](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/python/tutorials/gluon/02-layouts.py#L5-L102) ·
[Blocked layout definition](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/python/triton/experimental/gluon/language/_layouts.py#L60-L94) ·
[Blocked encoding to linear layout](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/lib/Dialect/TritonGPU/IR/LinearLayoutConversions.cpp#L832-L842)

`Value.toTensor` reads a logical coordinate through its assigned slot.
`Value.toTensor_convertLayout` proves that conversion preserves this Tensor
for arbitrary source slot values. `Expr.denote_toTensor_eq_erase` proves the
whole-expression equality, including conversions nested around any admitted
expression. `Expr.extract_denote_eq_erase` gives equality for every in-bounds
`Tensor.extract`. The examples check that lane 3, register 1 changes from
45 to 17 on `arange(10, 74)` while logical coordinate 7 still observes 17.
[Theorems](../../Silmaril/SSA/MLIR/Triton/Thms.lean) ·
[Lean examples](../../Silmaril/SSA/MLIR/Triton/Examples.lean)

Layout erasure is a logical interpretation across the frontend/IR layers.
Physical lowering would require a model of how a target implements each slot
permutation. Hardware shuffles, memory, concurrency, synchronization, and
cost are outside the theorem. The slice also excludes layout inference,
`assert_trivial=True`, overlapping or replicated layouts, multiple CTAs,
other ranks, extents and element types, and parsing or verifying general IR.

## Checks and provenance

```sh
lake build --wfail +Silmaril.SSA.MLIR.Triton.Examples
make check CHECK_TARGETS='+Silmaril.SSA.MLIR.Triton.Examples'
```

The Lean code and proofs are original. Operation semantics and the two
blocked slot assignments are specialized from the linked Triton **v3.7.0**
sources at commit `5f3f125e8f63c24613f1f73b937442864f263f94`, distributed
under the MIT license.
[Triton v3.7.0](https://github.com/triton-lang/triton/releases/tag/v3.7.0) ·
[Upstream license](https://github.com/triton-lang/triton/blob/5f3f125e8f63c24613f1f73b937442864f263f94/LICENSE)
