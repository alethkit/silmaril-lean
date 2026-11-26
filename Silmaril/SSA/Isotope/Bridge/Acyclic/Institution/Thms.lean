module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Signature.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Institution

/-! # Sentence naturality and satisfaction for the exact acyclic comparison -/

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Corridor)
open Isotope.LetCase.LocallyNameless (Derivation Tm)

variable {τ ε : Type} [TypeFormers τ]

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- The exact LetCase sentence round trip preserves both derivations. -/
@[simp] theorem compile_reify {P : InstrSig τ ε} (e : CaseEquation P) :
    compile (reify e) = e :=
  compile_reify_proof e

/-- Reification commutes with the existing LetCase institution's sentence
map after erasure into the existing positional λSSA syntax. -/
theorem reify_mapSentence {P Q : InstrSig τ ε} (g : P ⟶ Q) (e : CaseEquation P) :
    let e' := (((LetCase.inst Γ₀).map g).sen e : CaseEquation Q)
    ((reify e').2.1.toSSA 0, (reify e').2.2.toSSA 0) =
      (((reify e).2.1.toSSA 0).mapInstr (InstrSig.Hom.instr g),
       ((reify e).2.2.toSSA 0).mapInstr (InstrSig.Hom.instr g)) :=
  reify_mapSentence_proof g e

section FreydModels

open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Isotope.LetCase.LocallyNameless

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {J : V ⥤ C} [DistributiveFreydCategory J] {P : InstrSig τ ε}

/-- The algebra fold computes the exact distributive Freyd denotation. -/
theorem freydCaseAlgebra_denote (M : TypeModel τ V) (I : InstructionModel J M P.Instr)
    {n : Nat} {β : BoundCtx τ n} {A : τ}
    {t : Tm Empty P.Instr n} (d : Derivation P.Instr Γ₀ β t A) :
    letI := I
    Models.denote (freydCaseAlgebra J M I) d = Isotope.LetCase.Semantics.Categorical.denote J M d :=
  freydCaseAlgebra_denote_proof M I d

end FreydModels

section Models

variable {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] {P Q : InstrSig τ ε}

/-- Satisfaction of compiled equations in the actual LetCase algebra reduct
is equivalent to equality of the structured SSA region denotations. -/
theorem sat_compile_iff (K : CoherentRegionModel J P) (e : SSAEquation P) :
    ((LetCase.inst Γ₀).obj P).Sat K.caseAlgebra (compile e) ↔
      K.denoteSSA e.2.1 = K.denoteSSA e.2.2 :=
  sat_compile_iff_proof K e

/-- Reified equations in the coherent SSA model and the original LetCase
equations in its algebra reduct have the same truth value. -/
theorem sat_reify_iff (K : CoherentRegionModel J P) (e : CaseEquation P) :
    K.denoteSSA (reify e).2.1 = K.denoteSSA (reify e).2.2 ↔
      ((LetCase.inst Γ₀).obj P).Sat K.caseAlgebra e := by
  rw [← sat_compile_iff K (reify e), compile_reify]

/-- Along an existing primitive signature morphism the translated SSA
equation is satisfied exactly when the source equation is satisfied by the
LetCase signature reduct of the target model's algebra. -/
theorem sat_reify_map_iff (g : P ⟶ Q) (K : CoherentRegionModel J Q) (e : CaseEquation P) :
    let translated : CaseEquation Q := ((LetCase.inst Γ₀).map g).sen e
    K.denoteSSA (reify translated).2.1 = K.denoteSSA (reify translated).2.2 ↔
      ((LetCase.inst Γ₀).obj P).Sat (((LetCase.inst Γ₀).map g).mod.obj K.caseAlgebra) e :=
  (sat_reify_iff K _).trans (LetCase.satisfaction Γ₀ g K.caseAlgebra e)

/-- In the common model class independent derivations of a positional
LetCase judgment have equal denotations. -/
theorem denote_eq_of_sameTerm (K : CoherentRegionModel J P)
    {n : Nat} {β : BoundCtx τ n} {A : τ} {t : Tm Empty P.Instr n}
    (d d' : Derivation P.Instr Γ₀ β t A) :
    letI := K.instructions
    Isotope.LetCase.Semantics.Categorical.denote J K.types d =
      Isotope.LetCase.Semantics.Categorical.denote J K.types d' :=
  denote_eq_of_sameTerm_proof K d d'

/-- At a fixed signature, sentences go from LetCase into exact SSA and the
model functor goes from coherent SSA models to LetCase algebras. -/
@[expose] noncomputable def reifyCorridor (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] (P : InstrSig τ ε) :
    Corridor ((LetCase.inst Γ₀).obj P) (ssaRoom J P) where
  sen := reify
  mod := ShrinkHoms.inverse.{0} (Discrete (CoherentRegionModel J P)) ⋙
    Discrete.functor CoherentRegionModel.caseAlgebra
  sat K e := sat_reify_iff (ShrinkHoms.fromShrinkHoms K).as e

end Models
end Silmaril.Isotope.Institution.Acyclic
