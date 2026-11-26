# MLIR Shape and static tensors

`Silmaril.MLIR.Shape` models constants, constructors, queries, casts, concrete
broadcasting, a broadcast constraint, and a pure extent reduction for a small
fragment of the MLIR Shape dialect. It reuses `Tensor.Shape` for concrete
extents and `Tensor.Tensor` for the elements of a rank-one extent tensor.
[Definitions](../../Silmaril/SSA/MLIR/Shape/Defs.lean) ·
[Theorems](../../Silmaril/SSA/MLIR/Shape/Thms.lean) ·
[Extent operation definitions](../../Silmaril/SSA/MLIR/Shape/Extents/Defs.lean) ·
[Extent operation theorems](../../Silmaril/SSA/MLIR/Shape/Extents/Thms.lean) ·
[Variadic definitions](../../Silmaril/SSA/MLIR/Shape/Variadic/Defs.lean) ·
[Variadic theorems](../../Silmaril/SSA/MLIR/Shape/Variadic/Thms.lean) ·
[Reduction theorems](../../Silmaril/SSA/MLIR/Shape/Reduce/Thms.lean) ·
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

## Checked extent construction and queries

| Operation | Pinned type and folder boundary | Modeled fragment |
| --- | --- | --- |
| `shape.concat` | Each operand and the result independently have the shape-or-extent-tensor constraint. TableGen declares no custom verifier. The folder appends two dense extent constants and propagates poison. | Two concrete shape operands with a shape result, or two concrete extent tensors with an extent-tensor result. The shape form also propagates an invalid operand under the dialect's default rule. |
| `shape.dim` | Input is `AnyShaped`. The index operand and extent result each accept `!shape.size` or `index`. The inference trait uses the index operand's type and its compatibility hook accepts either result type. TableGen specifies an invalid size or undefined index result for an invalid or out-of-bounds operand index. The folder recognizes `shape.const_size` and `arith.constant` and returns an index attribute only for a ranked input and a known selected extent at an in-bounds constant index. | A static `Tensor.Tensor` and a signed mathematical `index` operand. Positions in `[0, rank)` return the selected extent, including zero. A negative position or one at or past rank gives an invalid `!shape.size` or an undefined `index` result. |
| `shape.split_at` | The operand and each of two results independently accept shape or extent tensor. The index operand accepts `!shape.size` or `index`. TableGen declares no custom verifier. The dense constant folder checks `[-rank, rank]`, adds rank to negative indices, and leaves out-of-range operations unfolded. A poison shape or index folds to two poison results. | A concrete shape and two shape results, or an extent tensor and two extent-tensor results, with a signed `index` operand. Both endpoints are admitted. An out-of-range extent-tensor split is undefined. The shape contract indicates an error outside the range and leaves its encoding across the two results unspecified. This case is outside the Lean shape-result fragment. |

[Pinned contracts for `dim`](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L308-L331) ·
[Pinned contracts for `split_at` and `concat`](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L703-L756) ·
[Pinned shape error rule and types](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeBase.td#L26-L42)

`concat?_ofStatic` and `concatExtentTensor_toShape` specify ordered append.
`dimSize_eq_known_iff` and `dimIndex_eq_defined_iff` characterize valid lookups.
`dimSize_append_left` and `dimSize_append_right` identify the selected operand
and its local index. `splitPoint?_eq_some_iff` gives the exact signed range and
normalized prefix length. `splitAtConcrete?_eq_some_iff` specifies both halves
by their concatenation and the prefix rank, while its lookup laws recover the
same extent on either side. The shape and extent-tensor round trips show that
splitting at the original left rank recovers the original operands and that
concatenating a successful split reconstructs the input. The examples cover
rank zero, zero extents, signed endpoints, and out-of-range indices.
[Checked extent theorems](../../Silmaril/SSA/MLIR/Shape/Extents/Thms.lean)

The `!shape.size` operand forms, dynamic or unranked shaped values for `dim`,
mixed shape and extent-tensor forms, declared result-type checks, and poison
are outside this slice. `concat?` leaves unknown shapes outside its domain
unless an invalid operand determines the result. `splitAt?` leaves invalid
and unknown input shapes outside its domain. The model uses mathematical ranks and indices
and assigns no target-width behavior. The pinned constant-fold tests provide
evidence for signed splitting and for leaving an out-of-range shape split
unfolded. The Lean laws concern operation values on the admitted fragment.
[Pinned `concat` folder](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L873-L889) ·
[Pinned `dim` folder and inference](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L1096-L1129) ·
[Pinned `split_at` folder](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L1920-L1950) ·
[Pinned constant-fold tests](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/test/Dialect/Shape/canonicalize.mlir#L13-L48)

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
Result type inference, declared extent-tensor lengths, error strings, and native
implementation correspondence are outside its scope.
[Pinned broadcast contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L57-L103) ·
[Pinned predicate contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L238-L269)

## Checked variadic broadcasting

| Operation | Modeled operand count | Pinned arity evidence |
| --- | --- | --- |
| `shape.broadcast` | One or more | TableGen describes two or more inputs. The verifier checks error-capable input and result types and imposes no count check. The folder forwards a single operand of matching type. A canonicalization handles the singleton cast case. The folder's other path assumes a nonempty operand list. A canonicalization pattern can produce an empty shape constant when no operands remain. The zero-operand operation is outside the model. |
| `shape.is_broadcastable` | Zero or more concrete shape views | TableGen declares variadic operands with no custom verifier. The folder returns true for fewer than two operands. |
| `shape.cstr_broadcastable` | Two or more concrete shape views | The custom verifier rejects fewer than two operands. |

[Pinned broadcast folder, verifier and rewrites](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L642-L748) ·
[Pinned predicate folder](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L1398-L1410) ·
[Pinned constraint folder and verifier](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L995-L1035)

`broadcastManyConcrete?` starts with the first operand and applies the checked
binary operation to the remaining operands. `BroadcastManyCompatible` says
that any two non-unit input extents at the same trailing axis agree. In
`BroadcastsManyTo`, the result rank is the greatest operand rank. Each result
axis has the unique non-unit input extent if present and one otherwise.
`broadcastManyConcrete?_eq_some_iff` and `broadcastManyConcrete?_axis_iff` give
this exact result for nonempty inputs. `compatible_iff_exists_broadcastsManyTo`
characterizes common compatibility, and `not_broadcastManyCompatible_iff`
identifies a conflicting pair of input extents. `broadcastManyConcrete?_perm`
proves that permuting operands preserves the exact result or failure. The four
`_pair` theorems recover the binary APIs.

`broadcastMany?` and `broadcastManyExtentTensor?` distinguish absence of
operands from an operand of rank zero. A single concrete operand is forwarded.
Incompatibility of concrete inputs gives an invalid shape or an undefined
extent-tensor result, according to the result form. A shape-valued broadcast
also propagates an invalid operand. Unknown operands without an invalid operand
are outside the modeled broadcast fragment. The predicate and constraint are
restricted to concrete inputs, including values obtained using `fromExtentTensor`.
`isBroadcastableMany?_ofStatic_eq_true_iff` and its false counterpart cover
common compatibility, including the vacuous predicate on zero operands.

`cstrBroadcastableMany?_passing_iff` and `cstrBroadcastableMany?_unsatisfied_iff`
identify when the concrete constraint provides a passing witness and when its
constraint is unsatisfied. The latter is an observation of the constraint,
with assertion lowering, runtime effects and general witness consumers outside
this slice. [Pinned constraint contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L874-L903) ·
[Pinned witness type](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeBase.td#L118-L133)

## Checked pure extent reduction

`shape.reduce` has one single-block region, a shape or extent tensor operand,
and a variadic initial tuple. The region is invoked in rank order, starting
at axis zero. The verifier checks the argument count and order of types. The
first argument is the axis of type `index`, the second is the extent of type
`index` for an extent tensor or `!shape.size` for a shape, and the remaining
arguments have the types of the initial operands in order. The builder uses
those initial types for the results and the parser resolves initial operands
against the result types. `shape.yield` checks its operand count and types
against the parent results. Its operands become the next carried tuple.
[Pinned `reduce` contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L503-L548) ·
[Pinned `yield` contract](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/include/mlir/Dialect/Shape/IR/ShapeOps.td#L673-L686) ·
[Pinned reduce builder, verifier and parser](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L1991-L2070) ·
[Pinned yield verifier](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Dialect/Shape/IR/Shape.cpp#L1901-L1914) ·
[Pinned verification fixtures](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/test/Dialect/Shape/invalid.mlir#L3-L79)

`ReduceBody` reuses `Pure.Code`, `Pure.Operands`, and `Arith.Env` for a
straight-line pure block with single-result primitives. Its arguments start
with the axis, the extent, and the
carried values. An explicit suffix supplies fixed captures from the enclosing
scope. A shared ordered width list types the initial tuple, carried arguments,
yield operands, and returned tuple, including the empty tuple. The scalar
profile reserves the selected width for `index` and uses the other widths for
signless integer types. It excludes a same-width integer type distinct from
`index`. `ReduceBody.run?` admits concrete extent tensors whose rank and entries
fit that width's nonnegative signed range. `ExtentTensor.ReduceFits.step_indices_exact`
shows that the axis and extent encodings then preserve their values.

The evaluator uses bounded tensor coordinates. `ReduceBody.denote_eq_foldl`
proves agreement with a left fold over the independent `Tensor.Shape` extent
list paired with its indices. `ReduceBody.denote_eq_foldl_of_step` transports the
result to a separately specified pure step. `ReduceBody.run?_of_rank_zero`
returns the initial tuple. The checked two-slot example uses a captured
increment and an order-sensitive trace. Its count includes zero extents, and
reversing the extents changes the trace. [Checked reduction examples](../../Silmaril/SSA/MLIR/Shape/Reduce/Examples/Thms.lean)

The checked fragment covers concrete extent tensors with total deterministic
body primitives. The `!shape.shape` form, including its `!shape.size` argument,
unknown or invalid shapes, poison, effects, and nested control flow are outside
this slice. `shape.yield` in a function library is also outside the slice. The
pinned conversion to `scf.for` supports extent tensors and maps block arguments
as axis, extracted extent, and carried tuple. The Lean proofs concern the
value-level fold. [Pinned conversion](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Conversion/ShapeToStandard/ShapeToStandard.cpp#L403-L452)

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
| `shape.concat` | Ordered append of concrete extents in the shape and extent-tensor forms. Invalid shape operands propagate to a shape result. |
| `shape.dim` | Static tensor and signed `index` operand with an index or size result. Out-of-range input gives undefined index or invalid size, respectively. |
| `shape.split_at` | Concrete shape or extent tensor split at a signed `index` in `[-rank, rank]`. Both extent-tensor results are undefined outside that range. |
| `shape.broadcast` | One or more concrete operands with right-aligned extents and order-independent results. The shape result propagates operand errors. The extent-tensor form has no defined result on incompatible extents. |
| `shape.is_broadcastable` | Boolean predicate for common compatibility of a list of concrete shape views, including zero or one operand. |
| `shape.cstr_broadcastable` | Passing witness or unsatisfied constraint on two or more concrete shape views. |
| `shape.reduce` | Rank-ordered fold over a concrete extent tensor with representable indices and a typed, single-block pure scalar body. |
| `shape.yield` | Typed carried-tuple terminator of the checked `shape.reduce` body. |
| `shape.shape_of` | Shape result for a static `Tensor.Tensor` via `shapeOf`. |
| `shape.rank` | Shape input and size output, including unknown rank and invalid shape. |
| `shape.get_extent` | Shape plus nonnegative index to size. Ranked inputs require an in-bounds index and can yield an unknown extent. An invalid shape yields an invalid size. |
| `shape.num_elements` | Shape to size, for fully concrete or invalid input. |
| `shape.to_extent_tensor` | Shape to a rank-one extent tensor with exact static length. Fully concrete input is defined and invalid input gives undefined behavior. |
| `shape.index_to_size` | Index to size, with undefined behavior on negative input. |
| `shape.size_to_index` | Size to index, with undefined behavior on unknown or invalid input. |

Cases outside the listed fragments of these nineteen operations are planned
only. In particular, `shape.from_extents` with `!shape.size` operands and the
behavior of either constructor on negative extents remain outside the model.
The other 21 pinned operations are all planned only, along with
`!shape.value_shape` and witness behavior beyond the stated constraint fragment.

| Area | Planned operations |
| --- | --- |
| Size arithmetic | `shape.add`, `shape.div`, `shape.max`, `shape.min`, `shape.mul` |
| Shape relations and combination | `shape.any`, `shape.meet`, `shape.shape_eq` |
| Constraints and witnesses | `shape.assuming`, `shape.assuming_all`, `shape.assuming_yield`, `shape.const_witness`, `shape.cstr_eq`, `shape.cstr_require` |
| Functions and regions | `shape.func`, `shape.function_library`, `shape.return` |
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
| [ShapeToStandard.cpp](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/lib/Conversion/ShapeToStandard/ShapeToStandard.cpp) | `f23c055fe4f250bafc7543a844a7b8b891a540916c792443b9e51291e136bfb8` |
| [Shape canonicalize.mlir](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/test/Dialect/Shape/canonicalize.mlir) | `f19290ac22b2e3db4eb86acebc6e31fc9355fc63ba92b8e53c184839acff1800` |
| [Shape invalid.mlir](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/test/Dialect/Shape/invalid.mlir) | `9f9e9a834b415eb7d3f5aa5861d291c45a62354b4e2da7fa43bb6dee6d2843a2` |
| [LLVM MLIR LICENSE.TXT](https://github.com/llvm/llvm-project/blob/cc45e189bc99870d26d50c5e3a3d215068e74880/mlir/LICENSE.TXT) | `94b301bb652ae351f5941655bf533f1a136300ad1396be7452c8a04ff2c91374` |

[Silmaril license](../../LICENSE)

```sh
lake build --wfail +Silmaril.SSA.MLIR.Shape.Examples.Thms +Silmaril.SSA.MLIR.Shape.Reduce.Examples.Thms
```

Each example module imports its Shape theorem headers directly. The existing
Lake glob discovers these modules.
