module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Functor.Thms

/-! # Change of type and primitive interpretation in the exact SSA comparison -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Acyclic (Operand)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
  [g.PreservesProducts] [g.PreservesSums]

/-- Translate an exact equation's input context and result type. -/
def mapTypingIndex (i : Theory.TypingIndex τ) : Theory.TypingIndex υ :=
  ⟨i.depth, i.bound.mapTypes g.ty, g.ty i.result⟩

/-- Apply the existing typed derivation map to both sides of a LetCase sentence. -/
def mapCaseSignature (e : CaseEquation P) : CaseEquation Q :=
  ⟨mapTypingIndex g e.1, Operand.mapSignature g e.2.1, Operand.mapSignature g e.2.2⟩

/-- Apply the existing structured code map to both sides of an SSA sentence. -/
def mapSSASignature (e : SSAEquation P) : SSAEquation Q :=
  ⟨mapTypingIndex g e.1, e.2.1.mapSignature g, e.2.2.mapSignature g⟩

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] {J : V ⥤ C}

/-- Reinterpret each source type by its image, transporting the target's chosen
product, unit, coproduct and initial-object data along type-former preservation. -/
@[instance_reducible] noncomputable def pullbackTypes (M : TypeModel υ V) : TypeModel τ V where
  obj := M.obj ∘ g.ty
  productIso A B :=
    eqToIso (congrArg M.obj (SignatureMap.PreservesProducts.product (g := g) A B)) ≪≫
      M.productIso (g.ty A) (g.ty B)
  unitIso :=
    eqToIso (congrArg M.obj (SignatureMap.PreservesProducts.unit (g := g))) ≪≫ M.unitIso
  coprodIso A B :=
    eqToIso (congrArg M.obj (SignatureMap.PreservesSums.coprod (g := g) A B)) ≪≫
      M.coprodIso (g.ty A) (g.ty B)
  emptyIsInitial := cast (congrArg (fun A : υ => IsInitial (M.obj A))
    (SignatureMap.PreservesSums.empty (g := g)).symm) M.emptyIsInitial

/-- Primitive arrows are inherited from the target and transported at the two
endpoints, using the same equality transport as the fixed-type reduct. -/
@[instance_reducible] def pullbackInstructions {M : TypeModel υ V} (I : InstructionModel J M Q.Instr) :
    InstructionModel J (pullbackTypes g M) P.Instr where
  denote f := transportArrow (M := M) (g.source f) (g.target f) (I.denote (g.instr f))

section Regions

open LambdaSSA.Semantics.Categorical (RegionDenotes RegionTypingCoherent ctxObj labelObj)

variable [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- The semantic transport law for pulling back a coherent region model.
A source witness has a target witness for the relabelled region at the
mapped contexts, with the same arrow after transport of its endpoints.
Both witnesses use the original relational semantics, including local CFGs. -/
def RegionWitnessPullback (K : CoherentRegionModel J Q) : Prop :=
  ∀ {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Region.HasType Γ r L}
    {a : J.obj (ctxObj (pullbackTypes g K.types) Γ) ⟶
      J.obj (labelObj (pullbackTypes g K.types) L)},
    (letI := pullbackInstructions g K.instructions
     RegionDenotes J (pullbackTypes g K.types) hr a) →
    ∃ (hr' : LambdaSSA.Region.HasType (Γ.map g.ty) (r.mapInstr g.instr) (L.map g.ty))
      (a' : J.obj (ctxObj K.types (Γ.map g.ty)) ⟶ J.obj (labelObj K.types (L.map g.ty))),
      (letI := K.instructions; RegionDenotes J K.types hr' a') ∧ HEq a a'

/-- The dependent reduct of the types and instructions of a coherent region
model, once the source's region coherence has been checked. -/
noncomputable def CoherentRegionModel.pullback (K : CoherentRegionModel J Q)
    (coh : letI := pullbackInstructions g K.instructions
           RegionTypingCoherent (Φ := P.Instr) J (pullbackTypes g K.types)) :
    CoherentRegionModel J P where
  types := pullbackTypes g K.types
  instructions := pullbackInstructions g K.instructions
  coherent := coh

end Regions

end Silmaril.Isotope.Institution.Acyclic
