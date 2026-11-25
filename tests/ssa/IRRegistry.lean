module

public import Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs

/-! Regression checks for the typed IR record handlers. -/

/-- error: silmaril ir_subset: Nat.zero must declare a type or a family of types -/
#guard_msgs in
silmaril ir_subset test.invalid := Nat.zero
  (family := mlir.llvm) (syntax_kind := simple_ssa) (title := "Not a type")

/-- error: silmaril ir_model: Silmaril.MLIR.Arith.Block.denote must take a program of type Silmaril.MLIR.LLVM.Block -/
#guard_msgs in
silmaril ir_model test.mismatched := Silmaril.MLIR.Arith.Block.denote
  (subset := mlir.llvm.scalar) (semantics := denotational) (title := "Mismatched program type")

/-- error: silmaril ir_model: no `silmaril institution mlir.llvm` is declared or imported -/
#guard_msgs in
silmaril ir_model test.wrong_target := Silmaril.MLIR.LLVM.Block.eval
  (subset := mlir.llvm.scalar) (semantics := operational) (title := "Wrong target kind")
  (institution := mlir.llvm)

/-- error: silmaril ir_model "mlir.llvm.scalar_eval" is already declared in Silmaril.LogicGraph.Nodes.SSA.MLIR.Defs -/
#guard_msgs in
silmaril ir_model mlir.llvm.scalar_eval := Silmaril.MLIR.LLVM.Block.eval
  (subset := mlir.llvm.scalar) (semantics := operational) (title := "Duplicate model")
