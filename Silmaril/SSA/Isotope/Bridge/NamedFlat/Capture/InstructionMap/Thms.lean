module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms

import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.InstructionMap

/-! # Naturality of executable capture closure -/

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Capture

universe u v w

variable {Φ : Type u} {Ψ : Type v} (f : Φ → Ψ)

variable {τ : Type w} {blocks exits n : Nat} {β : BoundCtx τ n}
  {g : FiniteCFG Φ blocks exits n} {closed : FiniteCFG Φ blocks exits 0}
  {input : LetCase.LocallyNameless.Tm Empty Φ 0}

/-- Closure transports the same capture context, relabels its producer,
and keeps the mapped code of every original block. -/
theorem Closes.mapInstr (h : Closes β input g closed) :
    Closes β (input.mapInstr f) (g.mapInstr f) (closed.mapInstr f) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.closes_mapInstr f h

variable [TypeFormers τ] [HasTy Φ τ] [HasTy Ψ τ]

/-- The closed capture producer retains the exact packed capture type. -/
theorem mapInput_hasType (profiles : InstructionMap.PreservesTypes (τ := τ) f)
    (h : LetCase.LocallyNameless.HasType Φ .nil .nil input (Region.packedInputType β.toList)) :
    LetCase.LocallyNameless.HasType Ψ .nil .nil (input.mapInstr f)
      (Region.packedInputType β.toList) :=
  Morphism.CaseSSA.hasType_of_erase (by simpa only [Morphism.CaseSSA.erase_mapInstr] using
    (Morphism.CaseSSA.erase_hasType h).mapInstr f profiles)

section Checker

variable {Base : Type w} [DecidableEq Base] [HasTy Φ (Ty Base)] [HasTy Ψ (Ty Base)]
  (profiles : InstructionMap.PreservesTypes (τ := Ty Base) f)

/-- Running the actual closure algorithm after relabelling returns the
mapped table on success. Failure is preserved as well. The projection
forgets the dependent typing and closure certificates. -/
theorem close_mapInstr (β : BoundCtx (Ty Base) n) (R : Fin blocks → Ty Base) (L : Fin exits → Ty Base)
    (g : FiniteCFG Φ blocks exits n) (hg : g.HasType β R L)
    (input : LetCase.LocallyNameless.Tm Empty Φ 0)
    (typed : LetCase.LocallyNameless.HasType Φ .nil .nil input (Region.packedInputType β.toList))
    (mapped : LetCase.LocallyNameless.HasType Ψ .nil .nil (input.mapInstr f)
      (Region.packedInputType β.toList)) :
    (close β R L (g.mapInstr f) (hg.mapInstr profiles) (input.mapInstr f) mapped).map Subtype.val =
      (close β R L g hg input typed).map (fun out => out.val.mapInstr f) :=
  Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.close_mapInstr f profiles β R L g hg input typed mapped

end Checker
end Silmaril.Isotope.Bridge.NamedFlat.Capture
