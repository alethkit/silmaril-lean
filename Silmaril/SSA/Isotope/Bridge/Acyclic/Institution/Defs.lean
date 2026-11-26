module

public import Silmaril.SSA.Isotope.Institution.LetCase.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Categorical.Realization.Thms
public import Mathlib.CategoryTheory.EssentiallySmall

/-! # Exact single-exit equations and their common coherent model class -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Logic.Institution (Room)
open Silmaril.Logic.Metatheory
open Silmaril.Isotope.Theory (TypingIndex)
open Silmaril.Isotope.LetCase.LocallyNameless
open LambdaSSA.Acyclic (Code)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso envPairHom freeLookup boundVar)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent ctxObj labelObj denoteRegion)

variable {τ ε : Type} [TypeFormers τ]

/-- An actual LetCase equation sentence at the empty named context. Bound
contexts and both exact typing derivations remain part of the sentence. -/
abbrev CaseEquation (P : InstrSig τ ε) :=
  ((LetCase.inst (ε := ε) (Ctx.nil : Ctx Empty τ)).obj P).Sen

/-- Single-exit structured SSA equation with a shared input and result sort. -/
abbrev SSAEquation (P : InstrSig τ ε) :=
  Σ i : TypingIndex τ, Code P.Instr i.bound i.result × Code P.Instr i.bound i.result

/-- Translate both sides forward to typed structured code. -/
def reify {P : InstrSig τ ε} (e : CaseEquation P) : SSAEquation P :=
  ⟨e.1, Code.ofLetCase e.2.1.2, Code.ofLetCase e.2.2.2⟩

/-- Translate both sides back to exact LetCase operands. -/
def compile {P : InstrSig τ ε} (e : SSAEquation P) : CaseEquation P :=
  ⟨e.1, e.2.1.toLetCase, e.2.2.toLetCase⟩

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)
local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairArrow" => LetIter.ProofRelevant.Semantics.Categorical.pair

/-- The operation algebra of the exact LetCase room at the empty named context. -/
abbrev CaseAlgebra (P : InstrSig τ ε) :=
  TheoryModel.Algebra.{0, 0, 0} (Models.signature P.Instr Γ₀)

section FreydModels

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J] {P : InstrSig τ ε}

/-- The carrier of a LetCase sort in a chosen value and computation model. -/
abbrev freydCaseArrow (M : TypeModel τ V) (i : TypingIndex τ) :=
  J.obj (envObj M Γ₀ i.bound) ⟶ J.obj (M.obj i.result)

/-- Interpret the exact LetCase operations in the chosen distributive Freyd model. -/
noncomputable def freydCaseOperation (M : TypeModel τ V) (I : InstructionModel J M P.Instr) :
    {i : TypingIndex τ} → (o : Models.Operation (Φ := P.Instr) Γ₀ i) →
      ((j : Fin o.arity) → freydCaseArrow J M (o.argSort j)) → freydCaseArrow J M i
  | _, .fv h, _ => J.map (freeLookup M _ h)
  | _, .bv i, _ => J.map (boundVar M i)
  | _, .op f, a => a 0 ≫ I.denote f
  | _, .let₁ (β := β) A _, a =>
      bindArrow J (a 0) (J.map (envSnocIso M Γ₀ β A).hom ≫ a 1)
  | _, .unit, _ => J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  | _, .pair A B, a => pairArrow J (a 0) (a 1) ≫ J.map (M.productIso A B).inv
  | _, .let₂ (β := β) A B _, a =>
      bindArrow J (a 0) (J.map (𝟙 _ ⊗ₘ (M.productIso A B).hom) ≫
        J.map (envPairHom M Γ₀ β A B) ≫ a 1)
  | _, .inl A B, a => a 0 ≫ J.map (coprod.inl ≫ (M.coprodIso A B).inv)
  | _, .inr A B, a => a 0 ≫ J.map (coprod.inr ≫ (M.coprodIso A B).inv)
  | _, .case (β := β) A B _, a =>
      caseWithContext J (a 0 ≫ J.map (M.coprodIso A B).hom)
        (J.map (envSnocIso M Γ₀ β A).hom ≫ a 1)
        (J.map (envSnocIso M Γ₀ β B).hom ≫ a 2)
  | _, .abort A, a => a 0 ≫ J.map (M.emptyIsInitial.to (M.obj A))

/-- The exact categorical LetCase algebra uses sequencing and coproducts. -/
noncomputable def freydCaseAlgebra (M : TypeModel τ V) (I : InstructionModel J M P.Instr) :
    CaseAlgebra P where
  Carrier := freydCaseArrow J M
  op := freydCaseOperation J M I

end FreydModels

section Models

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The common model class for the comparison with existing λSSA denotation.
Its objects are type and instruction interpretations in the chosen strong
Elgot Freyd category satisfying region typing coherence. -/
structure CoherentRegionModel (P : InstrSig τ ε) where
  types : TypeModel τ V
  instructions : InstructionModel J types P.Instr
  coherent : letI := instructions; RegionTypingCoherent (Φ := P.Instr) J types

variable {J} {P : InstrSig τ ε}

abbrev caseArrow (K : CoherentRegionModel J P) (i : TypingIndex τ) :=
  freydCaseArrow J K.types i

/-- The LetCase operations supplied by a coherent SSA model. -/
noncomputable def caseOperation (K : CoherentRegionModel J P)
    {i : TypingIndex τ} (o : Models.Operation (Φ := P.Instr) Γ₀ i)
    (a : (j : Fin o.arity) → caseArrow K (o.argSort j)) : caseArrow K i :=
  freydCaseOperation J K.types K.instructions o a

/-- The reduct of a coherent region model to an actual LetCase institution
model. Every operator acts by the exact categorical LetCase combinators. -/
noncomputable def CoherentRegionModel.caseAlgebra (K : CoherentRegionModel J P) :
    CaseAlgebra P where
  Carrier := caseArrow K
  op := caseOperation K

/-- The selected categorical denotation of the existing typed λSSA region. -/
noncomputable def CoherentRegionModel.denoteSSA (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {A : τ} (c : Code P.Instr β A) :
    J.obj (ctxObj K.types β.toList) ⟶ J.obj (labelObj K.types [A]) :=
  letI := K.instructions
  denoteRegion J K.types (c.toSSA_hasType (L := [A]) (exit := 0) rfl)

/-- The fixed-signature exact SSA room. The models are discrete so this
comparison requires no choice of a category of Freyd model morphisms. -/
noncomputable def ssaRoom (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := SSAEquation P
  Mod := Cat.of (ShrinkHoms (Discrete (CoherentRegionModel J P)))
  Sat K e :=
    let model := (ShrinkHoms.fromShrinkHoms K).as
    model.denoteSSA e.2.1 = model.denoteSSA e.2.2

end Models
end Silmaril.Isotope.Institution.Acyclic
