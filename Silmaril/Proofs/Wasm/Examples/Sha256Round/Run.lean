module

public import Silmaril.Wasm.Examples.Sha256Round.Defs
import Silmaril.Wasm.Verify.Kernel.Thms
meta import Silmaril.Wasm.Verify.Kernel.Defs

public section
namespace Silmaril.Proofs.Wasm.Examples.Sha256Round

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.SingleThreaded.Exec Silmaril.Wasm.Verify.Kernel
open Silmaril.Wasm.Examples.Sha256Round
open Silmaril.Crypto.SHA256.Kernel

set_option maxRecDepth 6000 in
theorem decode_fixture :
    exportedRound? fixture = some (signature, ⟨⟨0⟩, [], body⟩) := by
  kernel_rfl

private theorem choose_eq (e f g : Word) :
    ((g ^^^ f) &&& e) ^^^ g = Ch e f g := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  simp only [Ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

private theorem majority_eq (a b c : Word) :
    ((b ||| a) &&& c) ||| (b &&& a) = Maj a b c := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  simp only [Maj, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

private theorem rotate_eq (x : Word) (n : Nat) (hn : 0 < n) (hw : n < 32) :
    x.rotateLeft (32 - n) = x.rotateRight n := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt (show 32 - n < 32 by omega),
    show 32 - (32 - n) = n by omega]

private def compiled (x : Input) : Word :=
  let majority := ((x.b ||| x.a) &&& x.c) ||| (x.b &&& x.a)
  let s0 := x.a.rotateLeft 30 ^^^ x.a.rotateLeft 19 ^^^ x.a.rotateLeft 10
  let s1 := x.e.rotateLeft 26 ^^^ x.e.rotateLeft 21 ^^^ x.e.rotateLeft 7
  let choose := ((x.g ^^^ x.f) &&& x.e) ^^^ x.g
  majority + s0 + x.h + s1 + x.k + choose + x.w

private theorem compiled_eq (x : Input) (d : Word) :
    compiled x = (round x.a x.b x.c d x.e x.f x.g x.h x.k x.w).1 := by
  unfold compiled round Sigma0 Sigma1
  rw [majority_eq, choose_eq, rotate_eq x.a 2 (by decide) (by decide),
    rotate_eq x.a 13 (by decide) (by decide), rotate_eq x.a 22 (by decide) (by decide),
    rotate_eq x.e 6 (by decide) (by decide), rotate_eq x.e 11 (by decide) (by decide),
    rotate_eq x.e 25 (by decide) (by decide)]
  dsimp only
  ac_rfl

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1500000 in
private theorem run_compiled {H : Type} (o : GrowOracle) (x : Input) (s : Store H)
    (mi : ModuleInst) :
    runIK o fuel (entry x s mi) = (⟨s, x.frame mi, [constI32 (compiled x)]⟩, true) := by
  kernel_rfl

theorem run_fixture {H : Type} (o : GrowOracle) (x : Input) (d : Word) (s : Store H)
    (mi : ModuleInst) :
    runI o fuel (entry x s mi) =
      (⟨s, x.frame mi, [constI32 (round x.a x.b x.c d x.e x.f x.g x.h x.k x.w).1]⟩, true) := by
  rw [← runIK_eq, run_compiled, compiled_eq x d]

end Silmaril.Proofs.Wasm.Examples.Sha256Round
