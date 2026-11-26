module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.WitnessRegion

/-! # Forward type-changing transport of expression and region denotations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LambdaSSA.Semantics.Categorical (ctxObj labelObj Denotes RegionDenotes)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]

section Expressions

variable [DistributiveFreydCategory J]

/-- Every expression denotation witness in the pullback relabels to a
target witness with the same arrow after transport of the endpoints. -/
theorem mapTermWitness (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)
    {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm P.Instr} {A : τ}
    {ht : LambdaSSA.Tm.HasType Γ t A}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ) ⟶ J.obj ((pullbackTypes g M).obj A)}
    (d : letI := pullbackInstructions g I; Denotes J (pullbackTypes g M) ht f) :
    ∃ (ht' : LambdaSSA.Tm.HasType (Γ.map g.ty) (t.mapInstr g.instr) (g.ty A))
      (a : J.obj (ctxObj M (Γ.map g.ty)) ⟶ J.obj (M.obj (g.ty A))),
      (letI := I; Denotes J M ht' a) ∧ HEq f a :=
  mapTermWitness_proof g M I d

end Expressions

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]

/-- Forward relabelling transports the original region witness, including
the collective arrow and its local-label restrictions in a nonempty CFG. -/
theorem mapRegionWitness (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    {hr : LambdaSSA.Region.HasType Γ r L}
    {f : J.obj (ctxObj (pullbackTypes g M) Γ) ⟶ J.obj (labelObj (pullbackTypes g M) L)}
    (d : letI := pullbackInstructions g I; RegionDenotes J (pullbackTypes g M) hr f) :
    ∃ a : J.obj (ctxObj M (Γ.map g.ty)) ⟶ J.obj (labelObj M (L.map g.ty)),
      (letI := I; RegionDenotes J M (mapRegionTyping g hr) a) ∧ HEq f a :=
  mapRegionWitness_proof g M I d

/-- Forward witness transport supplies the law used to infer source
coherence and satisfaction from the coherent target model. -/
theorem regionWitnessPullback (K : CoherentRegionModel J Q) : RegionWitnessPullback g K := by
  intro Γ r L hr f d
  obtain ⟨a, da, e⟩ := mapRegionWitness g K.types K.instructions d
  exact ⟨mapRegionTyping g hr, a, da, e⟩

variable [FreydCategory.CentralUnit J]

/-- The existing exact SSA rooms admit a satisfaction-preserving corridor
along each type-former-preserving signature map. -/
noncomputable def ssaSignatureCorridor : ssaRoom J P ⟶ ssaRoom J Q :=
  ssaTypeCorridor g (regionWitnessPullback g)

end Silmaril.Isotope.Institution.Acyclic
