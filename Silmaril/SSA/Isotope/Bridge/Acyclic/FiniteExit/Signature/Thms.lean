module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Signature.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.FiniteExitSignature

/-! # The native and packed signature squares -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit

open Morphism (SignatureMap)
open Institution (InstrSig)
open Region (packedExitType)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}

omit [g.PreservesProducts] in
/-- Preserving the type formers preserves the exit sum, including its empty tail. -/
theorem packedExitType_map (L : LCtx τ) :
    g.ty (packedExitType L) = packedExitType (L.map g.ty) :=
  packedExitType_map_proof g L

/-- Mapping a native region changes primitives and leaves the label indices fixed. -/
theorem toSSA_mapSignature (c : FiniteExit P.Instr L β) :
    (c.mapSignature g).toSSA = c.toSSA.mapInstr g.instr :=
  toSSA_mapSignature_proof g c

/-- Packing commutes with the exact typed map up to the result-type transport. -/
theorem encode_mapSignature_heq (c : FiniteExit P.Instr L β) :
    HEq (c.encode.mapSignature g) (c.mapSignature g).encode :=
  encode_mapSignature_heq_proof g c

/-- Identity preserves the structured code at the mapped contexts. -/
theorem mapSignature_id_heq (c : FiniteExit P.Instr L β) :
    HEq (c.mapSignature (SignatureMap.id (Φ := P.Instr) (τ := τ) (ε := ε))) c :=
  mapSignature_id_heq_proof c

variable {κ ξ : Type} [TypeFormers κ] {S : InstrSig κ ξ}
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ) [h.PreservesProducts] [h.PreservesSums]

/-- Relabelling along the composite agrees with relabelling twice. -/
theorem mapSignature_comp_heq (c : FiniteExit P.Instr L β) :
    HEq (c.mapSignature (h.comp g)) ((c.mapSignature g).mapSignature h) :=
  mapSignature_comp_heq_proof g h c

end Silmaril.Isotope.LambdaSSA.Acyclic.FiniteExit
