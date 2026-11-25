module

public import Silmaril.SSA.MLIR.Frontend.Arith.Examples.Defs
public import Silmaril.SSA.MLIR.Arith.LetIter.Thms

/-! Check exact admission, rejected inputs, and execution through both lowerings. -/

public section

namespace Silmaril.MLIR.Frontend.Arith.Examples

open Silmaril.MLIR.Arith (instr word)
open Silmaril.MLIR.Arith.Examples (i1 i8)
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA

theorem triple_admitted : triple.elaborate = .ok ⟨[("flag", i1), ("x", i8)], i8, tripleBlock⟩ :=
  rfl

theorem triple_denote : tripleBlock.denote tripleEnv = 44#8 := rfl

theorem triple_lambdaSSA :
    Semantics.Region.Eval instr tripleEnv.toLambdaSSA tripleBlock.toLambdaSSA
      () 0 (word (w := i8) 44#8) () :=
  (tripleBlock.toLambdaSSA_eval_iff _ _ _).mpr ⟨rfl, congrArg (word (w := i8)) triple_denote.symm⟩

theorem triple_letIter :
    LetIter.Semantics.Eval instr Empty.elim tripleEnv.toLetIter tripleBlock.toLetIter
      () (word (w := i8) 44#8) () :=
  (tripleBlock.toLetIter_eval_iff _ _).mpr (congrArg (word (w := i8)) triple_denote.symm)

theorem square_admitted : square.elaborate = .ok ⟨[("x", i8), ("arg", i1)], i8, squareBlock⟩ :=
  rfl

theorem unknown_reference :
    Program.elaborate ⟨[], 8, .finish .ret "missing" 8⟩ = .error (.unknownReference "missing") :=
  rfl

theorem forward_reference :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letOp ⟨"sum", 8⟩ (.binary .addi "x" "later")
      (.letOp ⟨"later", 8⟩ (.constant 0) (.finish .ret "sum" 8))⟩ =
      .error (.unknownReference "later") := rfl

theorem duplicate_input :
    Program.elaborate ⟨[⟨"x", 1⟩, ⟨"x", 8⟩], 8, .finish .ret "x" 8⟩ =
      .error (.duplicateName "x") := rfl

theorem duplicate_result :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letOp ⟨"x", 8⟩ (.constant 2) (.finish .ret "x" 8)⟩ =
      .error (.duplicateName "x") := rfl

theorem operand_width_mismatch :
    Program.elaborate ⟨[⟨"x", 8⟩, ⟨"y", 1⟩], 8,
      .letOp ⟨"sum", 8⟩ (.binary .addi "x" "y") (.finish .ret "sum" 8)⟩ =
      .error (.widthMismatch "y" 8 1) := rfl

theorem return_width_mismatch :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .finish .ret "x" 1⟩ =
      .error (.widthMismatch "x" 8 1) := rfl

theorem zero_width :
    Program.elaborate ⟨[⟨"x", 0⟩], 8, .finish .ret "x" 8⟩ = .error (.zeroWidth (some "x")) :=
  rfl

theorem illegal_capture :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letRegion ⟨"r", 8⟩ "x" ⟨"arg", 8⟩
      (.finish .yield "x" 8) (.finish .ret "r" 8)⟩ = .error (.illegalCapture "x") := rfl

theorem nested_illegal_capture :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letRegion ⟨"r", 8⟩ "x" ⟨"arg", 8⟩
      (.letRegion ⟨"s", 8⟩ "arg" ⟨"inner", 8⟩ (.finish .yield "x" 8) (.finish .yield "s" 8))
      (.finish .ret "r" 8)⟩ = .error (.illegalCapture "x") := rfl

theorem region_local_does_not_escape :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letRegion ⟨"r", 8⟩ "x" ⟨"arg", 8⟩
      (.finish .yield "arg" 8) (.finish .ret "arg" 8)⟩ = .error (.unknownReference "arg") := rfl

theorem wrong_terminator :
    Program.elaborate ⟨[⟨"x", 8⟩], 8, .letRegion ⟨"r", 8⟩ "x" ⟨"arg", 8⟩
      (.finish .ret "arg" 8) (.finish .ret "r" 8)⟩ = .error (.wrongTerminator .yield .ret) := rfl

theorem unsupported_syntax :
    Program.elaborate ⟨[], 8, .unsupported "arith.addi overflow<nsw>"⟩ =
      .error (.unsupported "arith.addi overflow<nsw>") := rfl

end Silmaril.MLIR.Frontend.Arith.Examples
