module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.ExitPacking.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.JoinedInputPacking

/-! # Input record packing in the joined quotient -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.InputPacking

open CategoryTheory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "E" => Paper.Extension.Eqv (Seed)
local notation "Obj" => Paper.Extension.Singleton.ofType (Seed)

variable {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- A constructor record can replace the singleton input of a guarded region. -/
theorem unpack_valueBranches (hr : ValueBranches [packedInputType Γ] r L) :
    ValueBranches Γ (r.unpackInputs Γ) L :=
  JoinedInputPacking.unpack_valueBranches hr

/-- Destructuring the input preserves joined equations. -/
theorem pack_congr (h : E Γ r s L) :
    E [packedInputType Γ] (r.packInputsDestructure Γ) (s.packInputsDestructure Γ) L :=
  JoinedInputPacking.pack_congr h

/-- Substitution of the constructor record preserves joined equations. -/
theorem unpack_congr (h : E [packedInputType Γ] r s L) :
    E Γ (r.unpackInputs Γ) (s.unpackInputs Γ) L :=
  JoinedInputPacking.unpack_congr h

/-- Constructor β contracts every field of a packed input after unpacking. -/
theorem unpack_pack (hr : HasType Γ r L) :
    E Γ ((r.packInputsDestructure Γ).unpackInputs Γ) r L :=
  JoinedInputPacking.unpack_pack hr

/-- Guarded product η and the joined unit η recover the original input packet.
This applies also to the empty context and to arbitrary typed branch arguments. -/
theorem repack_unpack (hr : HasType [packedInputType Γ] r L) :
    E [packedInputType Γ] ((r.unpackInputs Γ).packInputsDestructure Γ) r L :=
  JoinedInputPacking.repack_unpack hr

/-- Packing the input reflects and preserves joined equations at the original interface. -/
theorem pack_eqv_iff (hr : HasType Γ r L) (hs : HasType Γ s L) :
    E [packedInputType Γ] (r.packInputsDestructure Γ) (s.packInputsDestructure Γ) L ↔ E Γ r s L :=
  ⟨fun h => (unpack_pack hr).symm.trans ((unpack_congr h).trans (unpack_pack hs)), pack_congr⟩

/-- Guarded regions in an exact finite input context, modulo the joined equations. -/
abbrev RegionClass (Γ : VCtx τ) (L : LCtx τ) :=
  Quot (fun r s : {r : Region Φ // ValueBranches Γ r L} => E Γ r.val s.val L)

/-- The class of a guarded region in its original context. -/
def regionClass (hr : ValueBranches Γ r L) : RegionClass (Φ := Φ) Γ L :=
  Quot.mk _ ⟨r, hr⟩

/-- The two input reindexings are inverse on guarded region classes. -/
def packEquiv (Γ : VCtx τ) (L : LCtx τ) :
    RegionClass (Φ := Φ) Γ L ≃ ExitPacking.RegionClass (Φ := Φ) (packedInputType Γ) L where
  toFun q := Quot.liftOn q (fun r => ExitPacking.regionClass r.property.packInputsDestructure)
    (fun _ _ h => Quot.sound (pack_congr h))
  invFun q := Quot.liftOn q (fun r => regionClass (unpack_valueBranches r.property))
    (fun _ _ h => Quot.sound (unpack_congr h))
  left_inv q := Quot.inductionOn q (fun r => Quot.sound (unpack_pack r.property.hasType))
  right_inv q := Quot.inductionOn q (fun r => Quot.sound (repack_unpack r.property.hasType))

/-- Product-packed inputs and tagged-sum exits identify guarded region classes
with joined singleton homs. -/
noncomputable def packedRegionEquiv (Γ : VCtx τ) (L : LCtx τ) :
    RegionClass (Φ := Φ) Γ L ≃ (Obj (packedInputType Γ) ⟶ Obj (packedExitType L)) :=
  (packEquiv Γ L).trans (ExitPacking.packEquiv (packedInputType Γ) L)

/-- Both sides compute by packing the specified guarded representative. -/
theorem packedRegionEquiv_apply (hr : ValueBranches Γ r L) :
    packedRegionEquiv Γ L (regionClass hr) = ExitPacking.packArrow hr.packInputsDestructure :=
  rfl

/-- Equality of the two packed singleton arrows is the joined equation at
the original guarded region interface. -/
theorem packedRegionEquiv_eq_iff (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) :
    packedRegionEquiv Γ L (regionClass hr) = packedRegionEquiv Γ L (regionClass hs) ↔ E Γ r s L := by
  rw [packedRegionEquiv_apply, packedRegionEquiv_apply, ExitPacking.packArrow_eq_iff]
  exact pack_eqv_iff hr.hasType hs.hasType

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.InputPacking
