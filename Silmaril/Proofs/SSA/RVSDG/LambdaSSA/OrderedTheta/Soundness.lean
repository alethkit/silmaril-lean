module

public import Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Model.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Region
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.OrderedTheta.Graph

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs

open CategoryTheory
open Silmaril.Elgot Isotope.LetIter.ProofRelevant.Semantics
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics.Monadic
open OrderedRuntime.Structured

universe u
variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε] [Bot ε]
  [Isotope.Subtyping τ] [TypeModel.{u,u} τ]
variable {A : τ} {r : Region Φ} {g : Loop Φ A}
set_option backward.isDefEq.respectTransparency false

section Monad

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  [InstructionModel Φ τ ε m]

theorem preserves (rel : Related A r g) :
    RegionDenotes (m := m) ε rel.typing (fun env =>
      (OrderedRuntime.Structured.Theta.denote.{u,u,u}
        (orderedModel (stepMap (m := m) (ε := ε))) g rel.checked).of (pack env.2) >>=
          fun output => pure (exit (unpack output))) := by
  cases rel with
  | loop s =>
    have norm := region_iterates (m := m) (ε := ε) s
    have eq : (fun env : Env [A] =>
        (show m (ValueTuple A) from
          (OrderedRuntime.Structured.Theta.denote.{u,u,u}
            (orderedModel (stepMap (m := m) (ε := ε))) (graph s) (graphChecked s)).of (pack env.2)) >>=
            fun output => pure (exit (unpack output))) =
        (fun env : Env [A] =>
          iter (stepMap (m := m) (ε := ε) s) env.2 >>= fun a => pure (exit a)) := by
      funext env
      rw [graph_iter (stepMap (m := m) (ε := ε)) s env.2, bind_assoc]
      simp only [pure_bind]
      rfl
    exact Eq.mpr (congrArg (RegionDenotes (m := m) ε (regionTyping s)) eq) norm

theorem ssa_denotes (rel : Related A r g) :
    RegionDenotes (m := m) ε rel.typing (fun env =>
      iter (stepMap (m := m) (ε := ε) rel.step) env.2 >>= fun a => pure (exit a)) := by
  cases rel with
  | loop s => exact region_iterates (m := m) (ε := ε) s

end Monad

section State

variable {σ : Type u} [InstructionModel Φ τ ε (StateT σ Part.{u})]

theorem preservesState (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a : TyDen A) (state : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run state =
      observe <$> OrderedRuntime.Structured.Theta.denoteTotal.{u,u,u}
        (orderedModel f) g rel.checked (point a state) := by
  rw [agrees]
  cases rel with
  | loop s => exact state_observation f s a state

omit [InstructionModel Φ τ ε (StateT σ Part.{u})] in
private theorem point_observe
    (p : Tuple (RuntimeValues (TyDen (τ := τ)) σ) (Threaded (carried A))) :
    point (observe p).1 (observe p).2 = p := by
  cases p with
  | cons a rest =>
    cases rest with
    | cons state tail =>
      cases tail
      rfl

theorem returns_iff (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a b : TyDen A) (initial final : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run initial = Part.some (b, final) ↔
      g.Returns (orderedModel f).toRVSDG (point a initial) (point b final) := by
  rw [preservesState rel f agrees, ← OrderedRuntime.Structured.Theta.denoteTotal_eq_some.{u,u,u}
    (orderedModel f) g rel.checked (point a initial) (point b final)]
  constructor
  · intro h
    have mapped := congrArg (fun z : Part (TyDen A × σ) => (fun p => point p.1 p.2) <$> z) h
    change Part.map (fun p : TyDen A × σ => point p.1 p.2)
      (Part.map observe (OrderedRuntime.Structured.Theta.denoteTotal.{u,u,u}
        (orderedModel f) g rel.checked (point a initial))) =
          Part.map (fun p : TyDen A × σ => point p.1 p.2) (Part.some (b, final)) at mapped
    rw [Part.map_map, Part.map_some] at mapped
    have identity : (fun p : TyDen A × σ => point p.1 p.2) ∘ observe = id :=
      funext point_observe
    rw [identity] at mapped
    exact (Part.map_id' (f := id) (fun _ => rfl) _).symm.trans mapped
  · intro h
    rw [h]
    rfl

theorem diverges_iff (rel : Related A r g) (f : Steps (τ := τ) Φ (StateM σ))
    (agrees : stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step = liftState f rel.step)
    (a : TyDen A) (initial : σ) :
    (iter (stepMap (m := StateT σ Part.{u}) (ε := ε) rel.step) a).run initial = Part.none ↔
      g.Diverges (orderedModel f).toRVSDG (point a initial) := by
  rw [preservesState rel f agrees, ← OrderedRuntime.Structured.Theta.denoteTotal_eq_none.{u,u,u}
    (orderedModel f) g rel.checked (point a initial)]
  simp only [Part.eq_none_iff']
  rfl

end State

end Silmaril.SSA.RVSDG.LambdaSSA.OrderedTheta.Proofs
