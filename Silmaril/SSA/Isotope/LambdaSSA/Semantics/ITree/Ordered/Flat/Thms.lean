module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Packing.Thms

/-! # The ordered satisfaction square for relabelled typed flat tables -/

public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

open Silmaril.Isotope.Morphism (SignatureMap)

universe u v w

variable {κ : Type (u + 1)} {Events : Type u → Type u}
  {Φ : Type v} {Ψ : Type w} [HasTy Φ (Ty κ)] [HasEff Φ Bool]
  [HasTy Ψ (Ty κ)] [HasEff Ψ Bool]

/-- A signature map with identity type component preserves both exact
primitive endpoints on the existing flat typing judgment. -/
theorem flatProfiles (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id) :
    InstructionMap.PreservesTypes (τ := Ty κ) g.instr :=
  ⟨fun f => (g.source f).trans (congrFun types _), fun f => (g.target f).trans (congrFun types _)⟩

/-- Packing the relabelled table gives the same exact singleton program as
relabelling the literal packed representative. Its typing proofs are
identified by proof irrelevance. -/
theorem Program.ofCFG_mapInstr (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    {blocks exits : Nat} {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ}
    {a : FiniteCFG Φ blocks exits 0} (ha : a.HasType .nil R D) :
    Program.ofCFG (ha.mapInstr (flatProfiles g types)) = (Program.ofCFG ha).map g types := by
  simp only [Program.ofCFG, Program.map, Program.mk.injEq, Region.mapInstr_renameVars]
  exact congrArg (Region.renameVars Nat.succ)
    (FiniteCFG.packedExecutionRegion_mapInstr g.instr (flatProfiles g types) ha)

/-- Satisfaction of two repacked mapped tables is satisfaction of the
original packed tables in the shared-event primitive reduct. -/
theorem satisfies_ofCFG_map_iff [AtomValues κ] (M : Model (κ := κ) Events Ψ)
    (g : SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool) (types : g.ty = id)
    (bottom : g.eff ⊥ = ⊥)
    {blocks blocks' exits : Nat} {R : Fin blocks → Ty κ} {R' : Fin blocks' → Ty κ}
    {D : Fin exits → Ty κ} {a : FiniteCFG Φ blocks exits 0} {b : FiniteCFG Φ blocks' exits 0}
    (ha : a.HasType .nil R D) (hb : b.HasType .nil R' D) :
    M.Satisfies (Program.ofCFG (ha.mapInstr (flatProfiles g types)))
      (Program.ofCFG (hb.mapInstr (flatProfiles g types))) ↔
    (M.reduct g types bottom).Satisfies (Program.ofCFG ha) (Program.ofCFG hb) := by
  rw [Program.ofCFG_mapInstr g types ha, Program.ofCFG_mapInstr g types hb, satisfies_map_iff M]

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
