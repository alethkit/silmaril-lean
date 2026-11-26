module

public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Flat.Institution.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution

open CategoryTheory
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered.FlatInstitution
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.Semantics (encodeValue encodeValue_injective)
open Silmaril.Elgot.ITree (TraceLE eq_iff_traceLE ret_inj)

universe u v

variable {κ : Type (u + 1)} {P Q S : FlatInstitution.Signature.{u, v} κ} {exits : Nat} {D : Fin exits → Ty κ}

private theorem table_congr {blocks : Nat} {R : Fin blocks → Ty κ}
    {a b : FiniteCFG P.Instr blocks exits 0} (eq : a = b)
    (ha : a.HasType .nil R D) (hb : b.HasType .nil R D) :
    Table.ofTyped (P := P) ha = Table.ofTyped hb := by
  subst b
  rfl

theorem table_map_id (a : Table P D) : a.map (𝟙 P) = a := by
  cases a with
  | mk blocks R code typed =>
    exact table_congr (FiniteCFG.mapInstr_id code) _ _

theorem table_map_comp (g : P ⟶ Q) (h : Q ⟶ S) (a : Table P D) :
    a.map (g ≫ h) = (a.map g).map h :=
  table_congr (FiniteCFG.mapInstr_comp g.toSignatureMap.instr h.toSignatureMap.instr a.code).symm _ _

variable [AtomValues κ] {Events : Type u → Type u}

attribute [local instance] typeModel

local notation "V" => AtomValues.carrier (κ := κ)
local notation "TM" => ModelTree Events

private theorem instructions_ext {I J : InstructionModel P.Instr (Ty κ) Bool TM}
    (h : I.denote = J.denote) (hp : I.denotePure = J.denotePure) : I = J := by
  cases I
  cases J
  cases h
  cases hp
  rfl

/-- Compatible models are determined by their erased primitive evaluation.
Injective return encoding recovers each typed tree, and purity recovers
the designated pure function from its return tree. -/
theorem model_ext_raw {M N : Model (κ := κ) Events P.Instr}
    (raw : M.raw = N.raw) : M = N := by
  have denote : M.instructions.denote = N.instructions.denote := by
    funext f x
    have left := M.compatible f x
    rw [raw] at left
    have encoded := left.symm.trans (N.compatible f x)
    apply eq_iff_traceLE.mpr
    simpa only [TraceLE.bind_pure_iff (encodeValue_injective V (instrTrg f))] using
      (eq_iff_traceLE.mp encoded)
  have denotePure : M.instructions.denotePure = N.instructions.denotePure := by
    funext f hf x
    apply (ret_inj (E := Events)).mp
    change (pure (M.instructions.denotePure f hf x) : TM _) = pure (N.instructions.denotePure f hf x)
    rw [← M.instructions.denote_pure f hf x, ← N.instructions.denote_pure f hf x, denote]
  have instructions := instructions_ext (P := P) denote denotePure
  cases M
  cases N
  cases instructions
  cases raw
  rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Interaction.Typed.Ordered.FlatInstitution
