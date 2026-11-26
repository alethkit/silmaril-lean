module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat

open Silmaril.Isotope.LambdaSSA

universe u v

variable {Φ : Type u} {Ψ : Type v} {labels n : Nat}

theorem erase_mapInstr (f : Φ → Ψ) (r : Flat Φ labels n) :
    (r.mapInstr f).erase = r.erase.mapInstr f := by
  induction r <;> simp_all [Flat.erase, Flat.mapInstr, Region.mapInstr,
    Silmaril.Isotope.Morphism.CaseSSA.erase_mapInstr]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat
