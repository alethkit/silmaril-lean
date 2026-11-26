module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.ForwardingTables.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.Observation.Thms

/-! # Binary tag separation for free simple types -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesSignature

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Paper.WithConstructorSequencing ForwardingTables

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

set_option backward.isDefEq.respectTransparency false

theorem not_separatesTags_iff (P : Ty α) :
    (¬ SeparatesTags (Φ := Φ) P) ↔ Paper.StructurallyEmpty P := by
  classical
  constructor
  · intro h
    have eq := Classical.not_not.mp h
    rw [← sumCofan_inl_sumIso_hom P P, ← sumCofan_inr_sumIso_hom P P,
      projection.map_comp, projection.map_comp] at eq
    have tagEq := (cancel_mono (projection.map (sumIso P P).hom)).mp eq
    rw [sumCofan_inl, sumCofan_inr] at tagEq
    have typed := (Paper.Extension.Singleton.ofRegion_eq_iff Seed
      (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))
      (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))).mp tagEq
    exact Paper.BoundSimulation.Obstruction.PairSequencing.structurallyEmpty_of_tagged_branches_eq P typed
  · intro hEmpty separate
    obtain ⟨initial⟩ := hEmpty.initial (Φ := Φ)
    exact separate (congrArg projection.map (initial.hom_ext coprod.inl coprod.inr))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ForwardingTablesSignature
