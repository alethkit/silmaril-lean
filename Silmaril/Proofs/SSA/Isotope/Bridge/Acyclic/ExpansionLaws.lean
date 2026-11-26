module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Expansion.Laws.Defs
public import Silmaril.Logic.Institution.Faithful
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

public section

set_option backward.isDefEq.respectTransparency false

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Logic.Institution (Corridor)
open Isotope.LetCase.LocallyNameless
open LetIter.Semantics.Categorical (TypeModel InstructionModel envObj envSnocIso boundVar)
open LetIter.ProofRelevant.Semantics.Categorical (bind duplicate extend)
open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

variable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

section Freyd

variable [DistributiveFreydCategory J] [FreydCategory.CentralUnit J]

private theorem denote_letReturn (M : TypeModel τ V) [InstructionModel J M P.Instr]
    {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}
    (d : Derivation P.Instr Γ₀ β t A) :
    Isotope.LetCase.Semantics.Categorical.denote J M (.let₁ d (.bv (ι := 0))) =
      Isotope.LetCase.Semantics.Categorical.denote J M d := by
  let f := Isotope.LetCase.Semantics.Categorical.denote J M d
  change extend J f ≫ (J.map (envSnocIso M Γ₀ β A).hom ≫
    J.map (boundVar M (Γ := Γ₀) (β := .snoc β A) 0)) = f
  have project :
      (envSnocIso M Γ₀ β A).hom ≫ boundVar M (Γ := Γ₀) (β := .snoc β A) 0 =
        CartesianMonoidalCategory.snd (envObj M Γ₀ β) (M.obj A) :=
    CartesianMonoidalCategory.associator_hom_snd_snd _ _ _
  rw [← J.map_comp, project]
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd_of_unit_central J (FreydCategory.CentralUnit.unit_central (J := J)),
    ← J.map_comp_assoc]
  simp [duplicate]

theorem freydCaseAlgebra_sat_letReturn_proof (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}
    (d : Derivation P.Instr Γ₀ β t A) :
    ((LetCase.inst Γ₀).obj P).Sat (freydCaseAlgebra J M I) (letReturnEquation d) := by
  let _ := I
  apply (LetCase.sat_iff Γ₀ P _ (.let₁ d (.bv (ι := 0))) d).mpr
  rw [freydCaseAlgebra_denote, freydCaseAlgebra_denote]
  exact denote_letReturn M d

end Freyd

theorem letReturnCountermodel_rejects_proof (P : InstrSig τ ε) :
    ¬ ((LetCase.inst Γ₀).obj P).Sat (letReturnCountermodel P) (unitLetReturn P) := by
  intro sat
  let d : Derivation P.Instr Γ₀ .nil (.unit : Tm Empty P.Instr 0) (unit : τ) := .unit
  have eq := (LetCase.sat_iff Γ₀ P (letReturnCountermodel P) (.let₁ d (.bv (ι := 0))) d).mp sat
  change true = false at eq
  cases eq

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]

theorem reifyCorridor_not_faithful_proof (P : InstrSig τ ε) :
    ¬ (reifyCorridor J P).Faithful := by
  intro reflects
  let e := unitLetReturn P
  have hs : (ssaRoom J P).Entails ((reifyCorridor J P).sen '' (∅ : Set (CaseEquation P)))
      ((reifyCorridor J P).sen e) := by
    intro N _
    let K := (ShrinkHoms.fromShrinkHoms N).as
    exact ((reifyCorridor J P).sat N e).mpr
      (freydCaseAlgebra_sat_letReturn_proof K.types K.instructions .unit)
  exact letReturnCountermodel_rejects_proof P
    (reflects ∅ e hs (letReturnCountermodel P) (fun _ h => h.elim))

end Silmaril.Isotope.Institution.Acyclic
