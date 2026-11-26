module

public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Region
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.NestedFeedback.Graph

/-! # Exact finite observations at the shared region boundary -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs

open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)
open Silmaril.Elgot (iter)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K D : τ} {r : Isotope.LambdaSSA.Region Φ} {g : Graph Φ A D}

theorem region_observe (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial =
      Part.map (exitTuple (A := A)) ((Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial) := by
  cases w with
  | generated s =>
    rw [region_round s coherent env, graph_observe (ε := ε)]
    simp only [StateT.run_bind, StateT.run_pure, Part.bind_eq_bind, Part.pure_eq_some, Part.bind_some_eq_map, Part.map_map]
    rfl

omit [HasTy Φ τ] [HasEff Φ ε] [Bot ε] [InstructionModel Φ τ ε (StateT σ Part.{u})] in
private theorem exit_injective : Function.Injective (exitTuple (A := A) (D := D) (σ := σ)) := by
  rintro ⟨(a | impossible), token⟩ ⟨(b | empty), final⟩ h
  · have val := congrArg (fun out : Point σ (Carrier A D) => out.get .head) h
    have state := congrArg (fun out : Point σ (Carrier A D) => out.get (.tail .head)) h
    exact Prod.ext (congrArg Sum.inl (Sum.inl.inj ((TypeModel.coprodEquiv D A).symm.injective val))) state
  · exact nomatch empty
  · exact nomatch impossible
  · exact nomatch impossible

theorem region_returns_iff (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (d : TyDen D) (initial final : σ) :
    returns (ε := ε) g env.2 initial d final ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.some (.inl d, final) := by
  refine (NestedTheta.Partial.observe_eq_some (wireModel (ε := ε)) g
    (entryTuple (env.2, initial)) (outputTuple (d, final))).symm.trans ?_
  change observe (ε := ε) g env.2 initial = Part.some (exitTuple (.inl d, final)) ↔ _
  rw [region_observe w coherent env initial, Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  exact ⟨fun ⟨x, hx, same⟩ => exit_injective same ▸ hx, fun hx => ⟨_, hx, rfl⟩⟩

theorem region_undefined_iff (w : Related A B K D r g)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    observe (ε := ε) g env.2 initial = Part.none ↔
      (Region.denote (ε := ε) (m := StateT σ Part.{u}) w.typing env).run initial = Part.none := by
  rw [region_observe w coherent env initial, Part.eq_none_iff', Part.eq_none_iff']
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Proofs
