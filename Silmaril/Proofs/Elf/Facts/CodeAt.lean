module

public import Silmaril.Elf.Facts.Defs
import Silmaril.Process.CLI.Cover.Thms

public section

namespace Silmaril.Proofs.Elf.Facts

open Silmaril.Elf
open Silmaril.X86.Link (Blob)

theorem codeAt_unique {F : Blob} {v : Nat} {xs ys : List (BitVec 8)} (hx : CodeAt F v xs)
    (hy : CodeAt F v ys) (hl : xs.length = ys.length) : xs = ys := by
  obtain ⟨A, hA, ph, hf, hr⟩ := hx
  obtain ⟨B, hB, ph', hf', hr'⟩ := hy
  have : A = B := Option.some.inj (hA.symm.trans hB)
  subst this
  rw [← hl, hf] at hf'
  cases hf'
  rw [← hl, hr] at hr'
  exact Silmaril.Process.CLI.valueLE_inj hl (Option.some.inj hr')

end Silmaril.Proofs.Elf.Facts
