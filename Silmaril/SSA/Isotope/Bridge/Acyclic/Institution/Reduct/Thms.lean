module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Reduct.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Reduct

/-! # Coherent region models are closed under primitive reduct -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Metatheory.TheoryModel
open LambdaSSA.Semantics.Categorical

variable {τ ε : Type} [TypeFormers τ] {P Q S : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- Restriction along a primitive map preserves categorical region coherence. -/
theorem CoherentRegionModel.restrict_coherent (g : P ⟶ Q) (K : CoherentRegionModel J Q) :
    letI := restrictInstructions g K.instructions
    RegionTypingCoherent (Φ := P.Instr) J K.types :=
  reduct_coherent_proof g K

/-- Restrict a coherent region model. Relabelling sends both denotation
witnesses to the same typed target region, so target coherence suffices. -/
@[expose] def CoherentRegionModel.reduct (g : P ⟶ Q) (K : CoherentRegionModel J Q) :
    CoherentRegionModel J P where
  types := K.types
  instructions := restrictInstructions g K.instructions
  coherent := K.restrict_coherent g

@[simp] theorem CoherentRegionModel.reduct_id (K : CoherentRegionModel J P) :
    K.reduct (𝟙 P) = K := by
  cases K
  rfl

@[simp] theorem CoherentRegionModel.reduct_comp (f : P ⟶ Q) (g : Q ⟶ S)
    (K : CoherentRegionModel J S) : K.reduct (f ≫ g) = (K.reduct g).reduct f := by
  cases K with
  | mk types instructions coherent =>
      simp only [CoherentRegionModel.reduct, restrictInstructions_comp_proof]
      rfl

/-- The reduct square agrees with the existing operation-algebra reduct,
including transport at primitives whose type equalities are propositional. -/
theorem CoherentRegionModel.caseAlgebra_reduct (g : P ⟶ Q) (K : CoherentRegionModel J Q) :
    (K.reduct g).caseAlgebra =
      Algebra.reductObj (LetCase.sigHom (Ctx.nil : Ctx Empty τ) g) K.caseAlgebra :=
  (caseAlgebra_reduct_proof g K).symm

/-- Categorical denotation in the reduct equals the denotation after relabelling. -/
theorem CoherentRegionModel.denoteRegion_reduct (g : P ⟶ Q) (K : CoherentRegionModel J Q)
    {Γ : LambdaSSA.VCtx τ} {r : LambdaSSA.Region P.Instr} {L : LambdaSSA.LCtx τ}
    (hr : LambdaSSA.Region.HasType Γ r L) :
    (letI := restrictInstructions g K.instructions; denoteRegion J K.types hr) =
    (letI := K.instructions
     denoteRegion J K.types (hr.mapInstr (InstrSig.Hom.instr g) ⟨g.source, g.target⟩)) :=
  denoteRegion_reduct_proof g K hr

end Silmaril.Isotope.Institution.Acyclic
