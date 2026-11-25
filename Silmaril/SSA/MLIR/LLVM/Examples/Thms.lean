module

public import Silmaril.SSA.MLIR.LLVM.Thms

/-! Regression examples for admission, execution, and the shared lowering. -/

namespace Silmaril.MLIR.LLVM.Examples

open Arith (Env Width)

private def i8 : Width := ⟨8, by decide⟩
private def i1 : Width := ⟨1, by decide⟩
private def tooWide : Width := ⟨2 ^ 23 + 1, by decide⟩

private def shared : Block [i1, i8] i8 :=
  .letOp (.constant 2#8)
    (.letOp (.binary .mul (.there (.there .here)) .here)
      (.letOp (.binary .add .here (.there .here)) (.ret .here)))

private def sharedSyntax : Syntax.Block [i1, i8] i8 :=
  .letOp (.constant 2#8)
    (.letOp (.binary .mul [] (.there (.there .here)) .here)
      (.letOp (.binary .add [] .here (.there .here)) (.ret .here)))

private def sharedArith : Arith.Block [i1, i8] i8 :=
  .letOp (.constant 2#8)
    (.letOp (.binary .muli (.there (.there .here)) .here)
      (.letOp (.binary .addi .here (.there .here)) (.yield .here)))

private def mixedInput : Env [i1, i8] := .cons 1#1 (.cons 200#8 .nil)

example : sharedSyntax.admit = .ok shared := rfl
example : sharedSyntax.run mixedInput = .ok (.ok 146#8) := rfl

example : Isotope.LetIter.Semantics.Eval Arith.instr Empty.elim mixedInput.toLetIter
    sharedArith.toLetIter () (Arith.word (w := i8) 146#8) () :=
  (shared.toLetIter_eval_iff sharedArith rfl mixedInput _).mpr ⟨146#8, rfl, rfl⟩

private def zeroOne : Env [i8, i8] := .cons 0#8 (.cons 1#8 .nil)

private def sub : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .sub [] .here (.there .here)) (.ret .here)

example : sub.run zeroOne = .ok (.ok 255#8) := rfl
example : (sub.admit.toOption.bind Block.toArith) = none := rfl

private def udiv : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .udiv [] (.there .here) .here) (.ret .here)

-- Unsigned and inexact, with no `exact` flag.
example : udiv.run (.cons 2#8 (.cons 255#8 .nil)) = .ok (.ok 127#8) := rfl
example : udiv.run zeroOne = .ok (.error .divisionByZero) := rfl
example : (udiv.admit.toOption.bind Block.toArith) = none := rfl

private def unusedDivision : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .udiv [] (.there .here) .here) (.ret (.there .here))

example : unusedDivision.run zeroOne = .ok (.error .divisionByZero) := rfl

private def rejectedTail : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .udiv [] (.there .here) .here)
    (.letOp (v := i8) .poison (.ret (.there .here)))

example : rejectedTail.run zeroOne = .error .poison := rfl

private def exactDivision : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .udiv [.exact] (.there .here) .here) (.ret .here)

example : exactDivision.run zeroOne = .error (.excludedFlags .udiv [.exact]) := rfl

private def flaggedAdd : Syntax.Block [i8, i8] i8 :=
  .letOp (.binary .add [.nsw, .nuw] .here (.there .here)) (.ret .here)

example : flaggedAdd.run zeroOne = .error (.excludedFlags .add [.nsw, .nuw]) := rfl

example : (Syntax.Block.letOp (Γ := []) (v := i8) .undef (.ret .here)).run .nil =
    .error .undef := rfl

example : (Syntax.Block.letOp (Γ := []) (v := i8) (.unsupported "llvm.load")
    (.ret .here)).run .nil = .error (.unsupportedOp "llvm.load") := rfl

example : (Syntax.Block.unsupportedTerminator (Γ := []) (w := i8) "llvm.br").run .nil =
    .error (.unsupportedTerminator "llvm.br") := rfl

example : (Syntax.Block.ret (Γ := [i8, tooWide]) .here).admit =
    .error (.unsupportedWidth tooWide.val) := rfl

example : (Syntax.Block.letOp (Γ := [i8]) (v := tooWide) .undef (.ret (.there .here))).admit =
    .error (.unsupportedWidth tooWide.val) := rfl

end Silmaril.MLIR.LLVM.Examples
