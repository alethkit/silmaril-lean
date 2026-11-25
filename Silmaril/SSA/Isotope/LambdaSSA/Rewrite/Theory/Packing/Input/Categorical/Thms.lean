module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputPackingCategorical

/-! # Categorical input packing for arbitrary exactly typed regions -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Region (packedInputType packedInputValue packedInputProjection
  packedInputValue_branchValue packedInputProjection_hasType)
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)

section Terms

variable [DistributiveFreydCategory J] {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The constructor record evaluates to the forward record isomorphism. -/
theorem packedInputValue_denotes (Γ : VCtx τ) :
    Denotes J M (packedInputValue_branchValue (Φ := Φ) Γ).hasType
      (J.map (inputRecordIso M Γ).hom) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packedInputValue_denotes J M Γ

/-- Reading a field of a pure record agrees with the original lookup after
decoding the record. -/
theorem packedInputProjection_denotes {Γ Δ : VCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At Γ i A) {ha : Tm.HasType Δ a (packedInputType Γ)}
    {p : ctxObj M Δ ⟶ M.obj (packedInputType Γ)} (da : Denotes J M ha (J.map p)) :
    Denotes J M (packedInputProjection_hasType hi ha)
      (J.map (p ≫ (inputRecordIso M Γ).inv ≫ lookup M i hi)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.packedInputProjection_denotes J M hi da

/-- Reading a field of the constructed input record has the same
denotation as the original variable. -/
theorem packedInputProjection_constructor_denotes {Γ : VCtx τ} {i : Nat} {A : τ}
    (hi : At Γ i A) :
    Denotes J M (packedInputProjection_hasType hi (packedInputValue_branchValue (Φ := Φ) Γ).hasType)
      (J.map (lookup M i hi)) := by
  simpa only [Iso.hom_inv_id_assoc] using
    packedInputProjection_denotes J M hi (packedInputValue_denotes (Φ := Φ) J M Γ)

end Terms

section Regions

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}

/-- Packing the inputs precomposes with the inverse environment isomorphism,
including across local block binders. -/
theorem RegionDenotes.packInputs {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.packInputs (J.map (packedInputIso M Γ).inv ≫ f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.regionDenotes_packInputs J M d

/-- Substituting the constructor record precomposes with the forward
environment isomorphism. -/
theorem RegionDenotes.unpackInputs {hr : Region.HasType [packedInputType Γ] r L}
    {f : J.obj (ctxObj M [packedInputType Γ]) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.unpackInputs (J.map (packedInputIso M Γ).hom ≫ f) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.regionDenotes_unpackInputs J M d

/-- Packing then unpacking admits the original denotation arrow. -/
theorem RegionDenotes.unpack_packInputs {hr : Region.HasType Γ r L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.packInputs.unpackInputs f := by
  simpa only [← J.map_comp_assoc, Iso.hom_inv_id, J.map_id, Category.id_comp] using
    (d.packInputs J M).unpackInputs J M

/-- Unpacking then packing admits the original singleton-input denotation arrow. -/
theorem RegionDenotes.pack_unpackInputs {hr : Region.HasType [packedInputType Γ] r L}
    {f : J.obj (ctxObj M [packedInputType Γ]) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M hr f) :
    RegionDenotes J M hr.unpackInputs.packInputs f := by
  simpa only [← J.map_comp_assoc, Iso.inv_hom_id, J.map_id, Category.id_comp] using
    (d.unpackInputs J M).packInputs J M

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem denoteRegion_packInputs (hr : Region.HasType Γ r L) :
    denoteRegion J M hr.packInputs = J.map (packedInputIso M Γ).inv ≫ denoteRegion J M hr :=
  ((denoteRegion_spec J M hr).packInputs J M).eq_denote J M |>.symm

theorem denoteRegion_unpackInputs (hr : Region.HasType [packedInputType Γ] r L) :
    denoteRegion J M hr.unpackInputs = J.map (packedInputIso M Γ).hom ≫ denoteRegion J M hr :=
  ((denoteRegion_spec J M hr).unpackInputs J M).eq_denote J M |>.symm

end Regions

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
