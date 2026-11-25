# MLIR Shape and static tensors

`Silmaril.MLIR.Shape` models shape-valued constants, queries, and casts for a
small fragment of the MLIR Shape dialect. It reuses `Tensor.Shape` for concrete
extents and `Tensor.Tensor` for the elements of a rank-one extent tensor.
[Definitions](../../Silmaril/SSA/MLIR/Shape/Defs.lean) ·
[Theorems](../../Silmaril/SSA/MLIR/Shape/Thms.lean) ·
[Static tensor definitions](../../Silmaril/SSA/MLIR/Tensor/Defs.lean)

## Values and admission

- `StaticShape` is compile-time information about a concrete tensor.
  `StaticShape.Admits` checks the declared rank and each known extent.
  An unranked declaration admits any rank. A missing extent in a
  ranked declaration admits any concrete extent at that coordinate.
- `ShapeValue` represents a value of `!shape.shape`. It can be unranked, ranked
  with unknown dimensions, or invalid. In a ranked value an unknown extent
  still occupies a coordinate. `Size` represents `!shape.size` and can be
  known, unknown, or invalid. Invalid values represent the dialect's errors.
- `Evaluation.undefined` describes an admitted cast whose behavior is
  undefined. For operations with a restricted domain, an outer `none` means
  that the operand lies outside this model's admitted fragment. For example,
  `toExtentTensor? .invalid` returns `some .undefined`, while an unranked
  operand returns `none`. Converting an unknown or invalid size to `index`
  has undefined behavior, as does converting a negative `index` to a size.

The model assumes decoded, well-typed operations. It uses mathematical
nonnegative extents and sizes and mathematical integers for indices. Claims
about target execution require represented operands and results to fit the
target index width. The model carries no error message payload and assigns
no behavior to out-of-scope cases.

## Checked static bridge

`ShapeValue.toStatic?_eq_some_iff` characterizes exactly which runtime values
reify to a given concrete shape. `ShapeValue.toStatic?_ofStatic` and
`shapeOf_toStatic?` check the round trips from an embedded shape and a static
tensor. `StaticShape.ofTensorShape_admits` connects the same extents to
the compile-time admission relation. `rank_ofStatic`, `getExtent?_ofStatic`
and `numElements?_ofStatic` identify the recovered rank, selected extent and
product of extents. `toExtentTensor?_ofStatic` and `extentTensor_coordinate`
identify the conversion and its contents at each in-bounds coordinate.
[Theorems](../../Silmaril/SSA/MLIR/Shape/Thms.lean)

The examples check that a static unknown admits a concrete dimension, a
runtime unknown extent is observable as an unknown size, an invalid shape
propagates to a size query, and converting it to an extent tensor has
undefined behavior. They distinguish a rank-zero tensor, whose element
count is one, from a tensor with a zero extent, whose element count is zero.
[Checked examples](../../Silmaril/SSA/MLIR/Shape/Examples/Thms.lean)

## Upstream operation coverage

The inventory covers the 40 operations in LLVM `llvmorg-22.1.0`, commit
`4434dabb69916856b824f68a64b029c67175e532`. “Checked” means the stated
fragment has a Lean definition and kernel-checked laws or boundary examples.
MLIR text admission and correspondence with the native implementation are
future work. [Dialect reference](https://mlir.llvm.org/docs/Dialects/ShapeDialect/) ·
[Pinned operation inventory](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td)

| Operation | Checked fragment |
| --- | --- |
| `shape.const_shape` | Shape-valued constants with concrete nonnegative extents via `ShapeValue.ofStatic`. |
| `shape.const_size` | Known nonnegative constants via `Size.known`. |
| `shape.shape_of` | Shape result for a static `Tensor.Tensor` via `shapeOf`. |
| `shape.rank` | Shape input and size output, including unknown rank and invalid shape. |
| `shape.get_extent` | Shape plus nonnegative index to size. Ranked inputs require an in-bounds index and can yield an unknown extent. An invalid shape yields an invalid size. |
| `shape.num_elements` | Shape to size, for fully concrete or invalid input. |
| `shape.to_extent_tensor` | Shape to a rank-one extent tensor with exact static length. Fully concrete input is defined and invalid input gives undefined behavior. |
| `shape.index_to_size` | Index to size, with undefined behavior on negative input. |
| `shape.size_to_index` | Size to index, with undefined behavior on unknown or invalid input. |

Cases outside the listed fragments of these nine operations are planned only.
The other 31 pinned operations are all planned only, along with
`!shape.value_shape` and `!shape.witness`.

| Area | Planned operations |
| --- | --- |
| Size arithmetic | `shape.add`, `shape.div`, `shape.max`, `shape.min`, `shape.mul` |
| Extent construction and queries | `shape.concat`, `shape.dim`, `shape.from_extent_tensor`, `shape.from_extents`, `shape.split_at` |
| Shape relations and combination | `shape.any`, `shape.broadcast`, `shape.is_broadcastable`, `shape.meet`, `shape.shape_eq` |
| Constraints and witnesses | `shape.assuming`, `shape.assuming_all`, `shape.assuming_yield`, `shape.const_witness`, `shape.cstr_broadcastable`, `shape.cstr_eq`, `shape.cstr_require` |
| Functions and regions | `shape.func`, `shape.function_library`, `shape.reduce`, `shape.return`, `shape.yield` |
| Value-shape pairs and debugging | `shape.debug_print`, `shape.value_as_shape`, `shape.value_of`, `shape.with_shape` |

## Provenance and checks

The Lean implementation is original Silmaril code under MIT. LLVM's
specifications and verifier are cited under Apache-2.0 WITH LLVM-exception.

| Pinned source | SHA-256 |
| --- | --- |
| [ShapeOps.td](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td) | `7a52b8cf1e3dd91b3b837bf1313dca7bb6c68e707d767d999c91b9f86719dfd1` |
| [ShapeBase.td](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Shape/IR/ShapeBase.td) | `5c94a6380d23f2b7efc8888813b058c6716c533beaae649cd8eea11f2a13173f` |
| [Shape.cpp](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/lib/Dialect/Shape/IR/Shape.cpp) | `b0f27808850cda7988fba288ddbf0d9663a1d1a0d6e324b884281f6d28354c6e` |

[Silmaril license](../../LICENSE) ·
[LLVM MLIR license](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/LICENSE.TXT)

```sh
lake build --wfail +Silmaril.SSA.MLIR.Shape.Examples.Thms
```

The example module imports the Shape theorem header directly. The existing
Lake glob discovers these modules.
