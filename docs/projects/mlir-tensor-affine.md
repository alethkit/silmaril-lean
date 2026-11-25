# Static tensor and pure affine slices of MLIR

The Tensor slice extends scalar Arith. The Affine slice uses Lean integers
and an independent semantics for a single-block loop. [Scalar Arith development](mlir.md)

## Static Tensor and tensor Arith

A shape `[d₀, …, dₙ₋₁]` indexes a tensor by the product of `Fin dᵢ`.
The empty product is `Unit`, so a rank-zero tensor has one element. A zero
extent at any axis makes the index domain empty. `eq_splat_rank_zero` and
`eq_of_zero_dim` give the respective extensional equality laws, and
`Index.false_of_zero_dim` rules out an admitted extract from an empty tensor.
[Definitions](../../Silmaril/SSA/MLIR/Tensor/Defs.lean) ·
[Theorems](../../Silmaril/SSA/MLIR/Tensor/Thms.lean)

| MLIR operation | Admitted denotation |
| --- | --- |
| `arith.constant` | The logical elements of an already matched dense integer attribute of static shape and positive signless bit width. |
| `tensor.splat` | Repeat one element at every index of the static result shape. |
| `tensor.extract` | Read one element. Each coordinate is in bounds and the index arity equals the rank by construction. |
| `arith.addi`, `arith.muli` | Combine elements at equal indices of operands of the same shape and positive signless bit width. With empty overflow flags, each scalar operation computes modulo $2^w$. |

`extract_binary` moves an extract through `arith.addi` or `arith.muli` to the
two operands. `lowerExtractBinary_denote` relates the demanded element to a
typed straight-line scalar Arith block that takes those extracted elements as
arguments. `lowerExtractBinary_eval_iff` characterizes the existing LambdaSSA
lowering of that scalar block. It exits at label zero with exactly the demanded
value. Tensor operands and the residual extracts stay in the source model.
[Tensor theorems](../../Silmaril/SSA/MLIR/Tensor/Thms.lean) ·
[Scalar Arith lowering](../../Silmaril/SSA/MLIR/Arith/Thms.lean)

`reindex` pulls elements back along a typed map from output indices to input
indices. It supplies a logical building block for operations such as transpose
once their specific shape and coordinate laws are supplied. The model assumes
admitted static extents, correctly decoded dense attributes and in-bounds
indices. Dynamic or unranked shapes, out-of-bounds execution, physical layouts,
attribute encoding, overflow flags, floating-point elements and a general SSA
rewrite pass are outside this checked slice. The polymorphic `Tensor`, `splat`,
`extract` and `reindex` use abstract element types.

## Affine maps and `affine.for`

`Expr` uses separately indexed dimension and symbol operands, integer literals,
addition and multiplication by integer constants. `Map` gives an ordered tuple
of results, and `apply` models the single-result `affine.apply` operation. Inputs
are assignments of mathematical integers to the two operand classes.
[Definitions](../../Silmaril/SSA/MLIR/Affine/Defs.lean)

`ForLoop` evaluates one affine expression for each bound. It takes a constant
positive step and one pure block given by its denotation. The block consumes
the induction value and the carried tuple and returns the tuple supplied to
`affine.yield`. Tuples with several values can use products and a loop with no
carried values can use `Unit`. The loop visits integer indices in order from
the lower bound, stopping before the upper bound.

`ForLoop.runs_iff_fold` proves that the loop relation admits exactly the result
of a left fold over its induction values. The enumeration terminates because
`(upper - iv).toNat` strictly decreases at each entered iteration.
`ForLoop.fold_of_ge` returns the initial tuple when the lower bound meets or
exceeds the upper bound. The observation in both theorems is the final carried
tuple. [Theorems](../../Silmaril/SSA/MLIR/Affine/Thms.lean)

The Affine slice excludes floor and ceiling division, remainder, multi-result
min/max bounds, checks for MLIR dimension and symbol binding rules, and
target-specific `index` widths and overflow. The body is a function on its
declared inputs. SSA region syntax, capture verification, memory, side effects
and a translation to LambdaSSA or LetIter are outside the loop theorem.

## StableHLO and Triton/Gluon

For a pure static-shape StableHLO fragment, reuse the index domains and logical
reindexing, then prove each operation's specific shape and element laws. A first
candidate is integer `stablehlo.add` with its own element-type contract.
`stablehlo.transpose` and `stablehlo.broadcast_in_dim` need explicit index maps
and their own verification conditions. Floating-point cases require a separate
element semantics. [StableHLO specification](https://openxla.org/stablehlo/spec)

For Triton/Gluon, these tensor functions can serve as the logical side of a
relation to lane- or thread-indexed representations. Layout conversions require
a relation showing which logical elements each thread holds and that the
conversion preserves the required observations. Masked memory, aliasing,
synchronization and parallel execution require additional state and effects.
The Affine fold proof applies to sequential pure carried state.
[Triton operations](https://triton-lang.org/main/dialects/TritonOps.html) ·
[Gluon layouts](https://triton-lang.org/main/getting-started/tutorials/gluon/layouts.html)

## Checks and provenance

```sh
lake build --wfail Silmaril.SSA.MLIR.Tensor.Thms Silmaril.SSA.MLIR.Affine.Thms
make check CHECK_TARGETS='Silmaril.SSA.MLIR.Tensor.Thms Silmaril.SSA.MLIR.Affine.Thms'
```

The Lean definitions and proofs are original code using the scalar Arith
development and Lean's finite index, bitvector, integer and list APIs. The MLIR
references specify the selected operations and types.
[Tensor operations](https://mlir.llvm.org/docs/Dialects/TensorOps/) ·
[Arith operations](https://mlir.llvm.org/docs/Dialects/ArithOps/) ·
[Affine operations and maps](https://mlir.llvm.org/docs/Dialects/Affine/) ·
[Builtin types and attributes](https://mlir.llvm.org/docs/Dialects/Builtin/)
