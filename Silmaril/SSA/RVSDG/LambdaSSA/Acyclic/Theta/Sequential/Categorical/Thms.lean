module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Categorical.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Phase
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Dispatch

/-! # Categorical factorization of the actual flat two-loop CFG -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical (RegionDenotes RegionTypingCoherent denoteRegion)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (F : V ⥤ C)

section Phases
variable [ElgotFreydCategory F] {X Y : V} {P O : C}

/-- A one-way dispatcher factors into the iterations at its two phases.
Only the phase injections used with uniformity must be pure. -/
theorem iterate_phases (first : F.obj X ⟶ P ⨿ F.obj X)
    (second : F.obj Y ⟶ O ⨿ F.obj Y) (handoff : P ⟶ F.obj Y) :
    F.map (coprod.inl : X ⟶ X ⨿ Y) ≫ iterate (phaseStep F first second handoff) =
      iterate first ≫ handoff ≫ iterate second :=
  Proofs.iterate_phases F first second handoff

end Phases

variable [StrongElgotFreydCategory F] [FreydCategory.CentralUnit F]
  (T : TypeModel τ V) [InstructionModel F T Φ]
variable {A B K M N H E D : τ}

omit [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory F] [FreydCategory.CentralUnit F]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C] in
theorem handoff_central [FreydCategory F] (M : τ) :
    PremonoidalCategory.IsCentral (F.map (handoffContext T M)) :=
  FreydCategory.image_central F _

/-- The flat CFG has the denotation of the two lowered θ computations in
source order, with the pure payload handoff between them. -/
theorem region_denotes (s : Loops Φ A B K M N H E D) :
    RegionDenotes F T (regionTyping s) (denote F T s) :=
  Proofs.region_denotes F T s

theorem denoteRegion_eq [RegionTypingCoherent (Φ := Φ) F T] (s : Loops Φ A B K M N H E D) :
    denoteRegion F T (regionTyping s) = denote F T s :=
  (region_denotes F T s).eq_denote.symm

theorem denoteRegion_sequential [RegionTypingCoherent (Φ := Φ) F T] (s : Loops Φ A B K M N H E D) :
    denoteRegion F T (regionTyping s) =
      denoteRegion F T (Theta.regionTyping s.first) ≫ F.map (handoffContext T M) ≫
        denoteRegion F T (Theta.regionTyping s.second) := by
  rw [denoteRegion_eq F T s, Theta.Categorical.denoteRegion_eq F T s.first,
    Theta.Categorical.denoteRegion_eq F T s.second]
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical
