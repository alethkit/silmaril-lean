module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Lift.Defs

public section

namespace Silmaril.Isotope.Institution.Acyclic

open CategoryTheory CategoryTheory.Limits
open Morphism (SignatureMap)
open LambdaSSA.Semantics.Categorical (RegionDenotes regionDenotes_exists)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ)

theorem regionTypingReflects_of_split_proof
    (back : SignatureMap Q.Instr P.Instr υ τ δ ε) [back.PreservesProducts] [back.PreservesSums]
    (types : Function.LeftInverse back.ty g.ty) (instructions : Function.LeftInverse back.instr g.instr) :
    RegionTypingReflects g := by
  intro Γ r L ht
  have hty : back.ty ∘ g.ty = id := funext types
  have hinstr : back.instr ∘ g.instr = id := funext instructions
  simpa only [List.map_map, hty, List.map_id, LambdaSSA.Region.mapInstr_comp, hinstr,
    LambdaSSA.Region.mapInstr_id] using (mapRegionTyping back ht)

variable [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

theorem regionWitnessLifts_iff_proof (K : CoherentRegionModel J Q) :
    RegionWitnessLifts g K ↔ RegionTypingReflects g := by
  constructor
  · intro lift Γ r L ht
    let _ := K.instructions
    obtain ⟨a, da⟩ := regionDenotes_exists J K.types ht
    obtain ⟨hr, _, _, _⟩ := lift da
    exact hr
  · intro reflects Γ r L ht a d
    let _ := pullbackInstructions g K.instructions
    let hr := reflects ht
    obtain ⟨f, df⟩ := regionDenotes_exists J (pullbackTypes g K.types) hr
    obtain ⟨b, db, e⟩ := mapRegionWitness g K.types K.instructions df
    exact ⟨hr, f, df, e.trans (heq_of_eq (K.coherent.denotes_eq db d))⟩

end Silmaril.Isotope.Institution.Acyclic
