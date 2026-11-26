# MLIR Shape and static tensors

`Silmaril.MLIR.Shape` models constants, constructors, queries, casts, and binary
broadcasting for a small fragment of the MLIR Shape dialect. It reuses
`Tensor.Shape` for concrete extents and `Tensor.Tensor` for the elements of a
rank-one extent tensor.
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
- `Evaluation.undefined` describes an admitted operation for which the
  contract provides no defined result. For operations with a restricted domain,
  an outer `none` means the inputs are outside the model's admitted fragment. For example,
  `toExtentTensor? .invalid` returns `some .undefined`, while an unranked
  operand returns `none`. Converting an unknown or invalid size to `index`
  has undefined behavior, as does converting a negative `index` to a size.

The model assumes decoded, well-typed operations on non-poison operands. It
uses mathematical nonnegative extents and sizes and mathematical integers for
indices. Claims about target execution require represented operands and
results to fit the target index width. The model carries no error message
payload and assigns no behavior to out-of-scope cases.

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

`fromExtents?_ofStatic` recovers a concrete shape from its nonnegative SSA
index operands in order. `fromExtents?_negative` proves rejection at any
position. `fromExtentTensor_extentTensor` and
`toExtentTensor?_fromExtentTensor` prove round trips between concrete shapes
and extent tensors. `rank_fromExtentTensor` and `getExtent?_fromExtentTensor`
specify the reconstructed rank and each in-bounds extent.

The examples check that a static unknown admits a concrete dimension, a
runtime unknown extent is observable as an unknown size, an invalid shape
propagates to a size query, and converting it to an extent tensor has
undefined behavior. They distinguish a rank-zero tensor, whose element
count is one, from a tensor with a zero extent, whose element count is zero.
Constructor examples cover empty inputs, zero extents, ordered coordinates,
and rejection of a negative index as outside the admitted fragment.
[Checked examples](../../Silmaril/SSA/MLIR/Shape/Examples/Thms.lean)

## Checked binary broadcasting

Two concrete operands are aligned at their trailing axes. Missing leading axes
are padded with ones. Equal extents are preserved, a one expands to the other
extent, and unequal non-unit extents are incompatible. In particular, one and
zero give zero in either order, while zero and two are incompatible. Rank-zero
shapes contribute only padding when paired with higher-rank shapes.
`broadcastConcrete?_eq_some_iff` specifies the result rank and all its extents.
`broadcastConcrete?_eq_none_iff` identifies an incompatible aligned axis
exactly when the computation fails.

`broadcast?_ofStatic_eq_some_iff` carries the result specification to
`!shape.shape`. `broadcastExtentTensor_eq_defined_iff` carries it to the
extent-tensor form, which takes two extent tensors and returns the exact
result extents when defined. The concrete predicate returns true exactly when
the corresponding broadcast produces a concrete shape or a defined extent
tensor, by `isBroadcastable?_ofStatic_eq_true_iff` and
`isBroadcastable?_fromExtentTensor_eq_true_iff`. A false result corresponds to
an invalid shape or to the absence of a defined extent tensor, by
`isBroadcastable?_ofStatic_eq_false_iff` and
`isBroadcastable?_fromExtentTensor_eq_false_iff`.

`fromExtentTensor` provides a concrete shape view for either operand of a
shape-valued broadcast or the predicate. An invalid input propagates in the
shape-valued broadcast, as specified by TableGen. Other non-concrete inputs
to `broadcast?`, and any non-concrete inputs to `isBroadcastable?`, are outside
the modeled domain. This slice covers two operands and the values they denote.
General variadic arities, result type inference, declared extent-tensor lengths,
error strings, and native implementation correspondence are outside its scope.
[Pinned broadcast contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L57-L103) ·
[Pinned predicate contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L238-L269)

## Upstream operation coverage

The inventory covers the 40 operations in llvm-project at commit
`cc45e189bc99870d26d50c5e3a3d215068e74880`. “Checked” means the stated
fragment has a Lean definition and kernel-checked laws or boundary examples.
MLIR text admission and correspondence with the native implementation are
future work. [Dialect reference](https://mlir.llvm.org/docs/Dialects/ShapeDialect/) ·
[Pinned operation inventory](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td)

| Operation | Checked fragment |
| --- | --- |
| `shape.const_shape` | Concrete nonnegative extents as a shape via `ShapeValue.ofStatic` or an extent tensor of exact static length via `extentTensor`. |
| `shape.const_size` | Known nonnegative constants via `Size.known`. |
| `shape.from_extents` | Variadic nonnegative `index` operands via `fromExtents?`, including zero operands for rank zero. |
| `shape.from_extent_tensor` | Rank-one tensor of known nonnegative indices via `fromExtentTensor`. The number of entries is the result rank and their order is preserved. |
| `shape.broadcast` | Two concrete operands with right-aligned extents. The shape result can carry invalidity, including propagated operand errors. The two-extent-tensor form has no defined extent-tensor result on incompatible extents. |
| `shape.is_broadcastable` | Boolean predicate on two concrete shape views with exact correspondence to binary broadcast on that domain. |
| `shape.shape_of` | Shape result for a static `Tensor.Tensor` via `shapeOf`. |
| `shape.rank` | Shape input and size output, including unknown rank and invalid shape. |
| `shape.get_extent` | Shape plus nonnegative index to size. Ranked inputs require an in-bounds index and can yield an unknown extent. An invalid shape yields an invalid size. |
| `shape.num_elements` | Shape to size, for fully concrete or invalid input. |
| `shape.to_extent_tensor` | Shape to a rank-one extent tensor with exact static length. Fully concrete input is defined and invalid input gives undefined behavior. |
| `shape.index_to_size` | Index to size, with undefined behavior on negative input. |
| `shape.size_to_index` | Size to index, with undefined behavior on unknown or invalid input. |

Cases outside the listed fragments of these thirteen operations are planned
only. In particular, `shape.from_extents` with `!shape.size` operands and the
behavior of either constructor on negative extents remain outside the model.
The other 27 pinned operations are all planned only, along with
`!shape.value_shape` and `!shape.witness`.

| Area | Planned operations |
| --- | --- |
| Size arithmetic | `shape.add`, `shape.div`, `shape.max`, `shape.min`, `shape.mul` |
| Extent construction and queries | `shape.concat`, `shape.dim`, `shape.split_at` |
| Shape relations and combination | `shape.any`, `shape.meet`, `shape.shape_eq` |
| Constraints and witnesses | `shape.assuming`, `shape.assuming_all`, `shape.assuming_yield`, `shape.const_witness`, `shape.cstr_broadcastable`, `shape.cstr_eq`, `shape.cstr_require` |
| Functions and regions | `shape.func`, `shape.function_library`, `shape.reduce`, `shape.return`, `shape.yield` |
| Value-shape pairs and debugging | `shape.debug_print`, `shape.value_as_shape`, `shape.value_of`, `shape.with_shape` |

## Provenance and checks

The Lean definitions, proofs and examples are independently authored Silmaril
code under MIT. They use the public operation contracts and Silmaril's Tensor
API. The cited LLVM TableGen and C++ files carry the SPDX identifier
`Apache-2.0 WITH LLVM-exception`.

| Pinned source | SHA-256 |
| --- | --- |
| [ShapeOps.td](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td) | `0816c5d0b8bbb17ac821048f49c699f6c214ddc69724a09ab9af163443c489e9` |
| [ShapeBase.td](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeBase.td) | `04d411df55d4ef3ed476d3e84905f8ce89d7f25e6fe21c26813f962ae2771766` |
| [Shape.cpp](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp) | `5d655eece44308a0907fbff7ec301434781067307919a94683e868268fee284e` |
| [LLVM MLIR LICENSE.TXT](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/LICENSE.TXT) | `94b301bb652ae351f5941655bf533f1a136300ad1396be7452c8a04ff2c91374` |

[Silmaril license](../../LICENSE)

```sh
lake build --wfail +Silmaril.SSA.MLIR.Shape.Examples.Thms
```

The example module imports the Shape theorem header directly. The existing
Lake glob discovers these modules.
