module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.LetCase.Signature.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeCaseSyntax
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.TypeChangeCaseAlgebra

/-! # The exact LetCase presentation over type changes -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel
open Silmaril.Logic.Institution (Inst Room)
open Morphism (SignatureMap)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
  [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "Δ₀" => (Ctx.nil : Ctx Empty υ)
local notation "Θ₀" => (Ctx.nil : Ctx Empty κ)

@[simp] theorem typeCaseHom_id :
    typeCaseHom (P := P) (Q := P) SignatureMap.id = 𝟙 (LetCase.presObj Γ₀ P) :=
  typeCaseHom_id_proof

theorem typeCaseHom_comp :
    typeCaseHom (h.comp g) = typeCaseHom g ≫ typeCaseHom h :=
  typeCaseHom_comp_proof g h

/-- The map restricts to the original operation translation on primitive maps. -/
theorem typeCaseHom_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q) :
    typeCaseHom f.toSignatureMap = (LetCase.pres Γ₀).map f :=
  typeCaseHom_primitive_proof f

/-- The presentation's initial-algebra fold is the typed syntax map. -/
theorem typeCaseHom_translate (e : CaseEquation P) :
    PresSig.mapEquation (typeCaseHom g) e = mapCaseSignature g e :=
  typeCaseHom_translate_proof g e

/-- The existing LetCase presentations with their type-changing operation maps. -/
def letCaseTypePres : TypeSignature ⥤ PresSig.{0, 0, 0} where
  obj P := LetCase.presObj (Ctx.nil : Ctx Empty P.types) P.prim
  map f := typeCaseHom f.signatureMap
  map_id _ := typeCaseHom_id
  map_comp f g := typeCaseHom_comp f.signatureMap g.signatureMap

/-- The exact LetCase institution over changing types, via presented syntax. -/
def letCaseTypeInst : TypeSignature ⥤ Room.{0, 0, 1} :=
  letCaseTypePres ⋙ PresSig.inst

/-- The bundled exact LetCase institution over changing types. -/
def letCaseTypeInstitution : Inst.{1, 0, 0, 0, 1} :=
  ⟨TypeSignature, letCaseTypeInst⟩

/-- The exact SSA equation map restricts to the existing primitive fold. -/
theorem mapSSASignature_primitive {P Q : InstrSig τ ε} (f : P ⟶ Q) (e : SSAEquation P) :
    mapSSASignature f.toSignatureMap e = mapEquation f e :=
  mapSSASignature_primitive_proof f e

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- The LetCase algebra of a coherent SSA pullback is the actual algebra
reduct along the mapped operation signature. -/
theorem caseAlgebra_typeChange (K : CoherentRegionModel J Q) :
    (K.pullbackOfWitness g (regionWitnessPullback g K)).caseAlgebra =
      Algebra.reductObj (PresSig.toHom (typeCaseHom g)) K.caseAlgebra :=
  (caseAlgebra_pullback_proof g K).symm

end Silmaril.Isotope.Institution.Acyclic
