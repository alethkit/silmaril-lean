module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical.Wires.State

/-! # Categorical recovery and its exact-token specialization -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical

section Freyd
open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaSSA.Semantics.Categorical (RegionTypingCoherent denoteRegion)
open Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (F : V ⥤ C) [StrongElgotFreydCategory F]
  [FreydCategory.CentralUnit F] (T : TypeModel τ V) [InstructionModel F T Φ]
  [RegionTypingCoherent (Φ := Φ) F T]
variable {A B K M N H E D : τ} {g : Wires.Graph Φ A M E D}

/-- The checked parse determines the two lowered computation arrows and
the same sequential denotation for the recovered flat CFG. -/
theorem raised_denoteRegion_eq (d : Wires.Reverse.Decomposition g B K N H) :
    denoteRegion F T (Wires.Reverse.raise d).2.typing = denote F T d.view.decode := by
  have typing : (Wires.Reverse.raise d).2.typing = regionTyping d.view.decode := Subsingleton.elim _ _
  rw [typing]
  exact denoteRegion_eq F T d.view.decode

end Freyd

section State
open Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA.Semantics.Monadic
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Agreement (RegionCoherent)

universe u
variable {τ Φ ε σ : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ] [InstructionModel Φ τ ε (StateT σ Part.{u})]
variable {A B K M N H E D : τ}

theorem stateDenote_eq (s : Loops Φ A B K M N H E D) (env : Env [A])
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u})) :
    stateDenote (ε := ε) (σ := σ) s env =
      Region.denote (ε := ε) (m := StateT σ Part.{u}) (regionTyping s) env :=
  Proofs.stateDenote_eq s env coherent

/-- After specialization, the already-checked graph observes exactly the
Kleisli result encoded with its final explicit token. -/
theorem state_observe (s : Loops Φ A B K M N H E D)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Wires.observe (ε := ε) (Wires.graph s) env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := M)) ((stateDenote (ε := ε) s env).run initial) := by
  rw [stateDenote_eq s env coherent]
  exact (Wires.Related.loops s).region_observe coherent env initial

theorem raised_state_observe {g : Wires.Graph Φ A M E D} (d : Wires.Reverse.Decomposition g B K N H)
    (coherent : RegionCoherent (τ := τ) (Φ := Φ) (ε := ε) (m := StateT σ Part.{u}))
    (env : Env [A]) (initial : σ) :
    Wires.observe (ε := ε) g env.2 initial =
      Part.map (ExplicitRuntime.exitTuple (A := M)) ((stateDenote (ε := ε) d.view.decode env).run initial) :=
  (congrArg (fun h => Wires.observe (ε := ε) h env.2 initial) d.wiring).symm.trans
    (state_observe d.view.decode coherent env initial)

end State

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Categorical
