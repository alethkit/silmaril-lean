module

public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.InstructionMap

/-! # Erasure and exact typing under flat instruction relabelling -/

public section

namespace Silmaril.Isotope.LambdaSSA

universe u v w

variable {Φ : Type u} {Ψ : Type v} {labels n blocks exits : Nat}

@[simp] theorem Flat.erase_mapInstr (f : Φ → Ψ) (r : Flat Φ labels n) :
    (r.mapInstr f).erase = r.erase.mapInstr f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Flat.erase_mapInstr f r

@[simp] theorem FiniteCFG.erase_mapInstr (f : Φ → Ψ) (g : FiniteCFG Φ blocks exits n) :
    (g.mapInstr f).erase = g.erase.mapInstr f := by
  simp [FiniteCFG.mapInstr, FiniteCFG.erase, Region.mapInstr]

variable {τ : Type w} [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]
  {f : Φ → Ψ} (profiles : InstructionMap.PreservesTypes (τ := τ) f)
include profiles

theorem Flat.HasType.mapInstr {L : Fin labels → τ} {β : BoundCtx τ n} {r : Flat Φ labels n}
    (h : r.HasType L β) : (r.mapInstr f).HasType L β :=
  Flat.hasType_of_erase (by simpa only [Flat.erase_mapInstr] using h.erase.mapInstr f profiles)

/-- The mapped table keeps the same captures, block parameter types and exit types. -/
theorem FiniteCFG.HasType.mapInstr {R : Fin blocks → τ} {L : Fin exits → τ}
    {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n} (h : g.HasType β R L) :
    (g.mapInstr f).HasType β R L :=
  ⟨h.entry.mapInstr profiles, fun i => (h.block i).mapInstr profiles⟩

end Silmaril.Isotope.LambdaSSA
