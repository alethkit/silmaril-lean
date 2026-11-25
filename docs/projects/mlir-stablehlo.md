# Static integer StableHLO

The slice models `stablehlo.constant` and `stablehlo.add` on static ranked
tensors with integer elements. Extents are nonnegative. A rank-zero tensor
has one element and a shape with a zero extent has no observable elements.
It uses Silmaril's existing Tensor index domains and scalar Arith blocks.
[Definitions](../../Silmaril/SSA/MLIR/StableHLO/Defs.lean) ·
[Tensor and Arith design](mlir-tensor-affine.md)

## Admitted operations and types

Widths are exactly 2, 4, 8, 16, 32 and 64 bits. For each width `N`, the
StableHLO v1.13.0 specification calls the signed type `siN` and the unsigned
type `uiN`. The dialect implementation at that revision spells the signed case
with MLIR's signless `iN` and the unsigned case with `uiN`. `IntType` retains
the distinction even when the bits have the same width. The `i1` Boolean type
and its OR semantics for `stablehlo.add` are outside the slice.
[Specification types](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/docs/spec.md#types) ·
[Dialect type definitions](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/stablehlo/dialect/Base.td#L48-L57)

| Operation | Contract |
| --- | --- |
| [`stablehlo.constant`](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/docs/spec.md#constant) | Takes the decoded logical elements of a dense integer `value` attribute, with splats already expanded. The attribute has the exact shape and element type of the result. |
| [`stablehlo.add`](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/docs/spec.md#add) | Takes two tensors and adds elements at equal indices. Both operands and the result share one shape and one element type. The operation has no operation-specific attributes. |

The spec leaves integer overflow implementation-defined. This model fixes
the v1.13.0 reference interpreter behavior of wrapping at the element width
through `APInt` addition. The result bits are the sum modulo `2^N` for either
signedness. The two interpretations use two's-complement integers and unsigned
natural numbers, respectively, before encoding the sum back into `N` bits.
[Specification errors](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/docs/spec.md#errors) ·
[Interpreter addition](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/stablehlo/reference/Element.cpp#L350-L361)

The input contract starts at typed, decoded values. It excludes text parsing,
literal validation, tensor encodings and physical layouts, dynamic extents,
broadcasting, floating-point, complex and quantized elements, and SSA programs.

## Checked correspondence

- `IntType.add_eq_addi` proves that either StableHLO integer interpretation
  gives the same bits as the signless Arith addition at the same width.
- `extract_constant` and `extract_add` identify each in-bounds observation
  with the extraction from a dense `arith.constant` or flag-free tensor
  `arith.addi` in the existing Tensor model.
- `lowerConstantAt_denote` checks a closed scalar Arith block for the demanded
  constant element. `lowerAdd_denote` checks the existing scalar Arith add
  block fed by the two residual operand extracts. Both blocks return the
  demanded bits. The add correspondence assumes the two logical extractions
  have supplied scalar operands.

[Theorem statements](../../Silmaril/SSA/MLIR/StableHLO/Thms.lean) ·
[Examples](../../Silmaril/SSA/MLIR/StableHLO/Examples/Thms.lean)

The Lean code is original and reuses the Silmaril Tensor and Arith APIs. The
upstream StableHLO tag `v1.13.0` resolves to commit
`20b8ee58da51d373ab73331f39236dadba0b942b`. Its Apache-2.0 sources are cited for
the operation contracts, type spellings and reference overflow behavior.
[Upstream license](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/LICENSE) ·
[Upstream LLVM pin](https://github.com/openxla/stablehlo/blob/20b8ee58da51d373ab73331f39236dadba0b942b/build_tools/llvm_version.txt) ·
[Arith operation reference](https://github.com/llvm/llvm-project/blob/fc44a4fcd3c54be927c15ddd9211aca1501633e7/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td#L165-L248)

```sh
lake build --wfail +Silmaril.SSA.MLIR.StableHLO.Examples.Thms
make check CHECK_TARGETS=+Silmaril.SSA.MLIR.StableHLO.Examples.Thms
```
