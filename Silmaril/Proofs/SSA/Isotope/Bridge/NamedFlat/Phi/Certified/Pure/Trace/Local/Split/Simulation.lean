module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Transfer

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split (Witness)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Pending)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree ret vis diverge cases_visible diverge_bind vis_bind)
open LambdaSSA.Semantics.Interaction (Primitive)

universe u v
variable {V W K J α : Type (u + 1)} {F : Type v} {E : Type u → Type u}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (instr : Primitive E F α) (source : Graph V K F)

private abbrev Left := Tree E (BodyResult V K α)
private abbrev Right := Tree E (BodyResult W J α)

private noncomputable def mapBody (t : Left (E := E) (V := V) (K := K) (α := α)) :
    Right (E := E) (W := W) (J := J) (α := α) :=
  Sum.map id (routed plan) <$> t

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem map_pure (a : BodyResult V K α) :
    mapBody plan (pure a : Left (E := E)) = pure (Sum.map id (routed plan) a) := by
  simp [mapBody]

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem map_diverge :
    mapBody plan (diverge : Left (E := E) (V := V) (K := K) (α := α)) = diverge := by
  simp [mapBody, ← bind_pure_comp]

omit [DecidableEq V] [DecidableEq W] [DecidableEq J] in
private theorem map_vis {R : Type u} (event : E R)
    (k : R → Left (E := E) (V := V) (K := K) (α := α)) :
    mapBody plan (vis event k) = vis event (fun reply => mapBody plan (k reply)) := by
  simp only [mapBody, ← bind_pure_comp, vis_bind]

omit [DecidableEq V] in
private theorem forward_cases (checked : plan.hasBackedge source = true)
    (p : Pending V K (Value α)) :
    routed plan p = aligned plan p ∨
      stepTree instr (plan.rewrite source) (routed plan p) = pure (.inr (aligned plan p)) := by
  obtain ⟨control, store⟩ := p
  cases control with
  | returned value => exact .inl rfl
  | jump pred target =>
    by_cases selected : plan.selected pred target
    · obtain ⟨rfl, rfl⟩ := selected
      apply Or.inr
      simpa [routed, aligned, Plan.rekey, Plan.selected] using step_forward plan instr source checked store
    · exact .inl (by simp [routed, aligned, Plan.rekey, selected])

private def forwardSimulation (checked : plan.hasBackedge source = true) :
    Simulation instr instr source (plan.rewrite source) where
  boundary l r := r = aligned plan l
  residual l r := r = mapBody plan l
  atBoundary := by
    rintro l _ rfl
    exact step_aligned plan instr source l
  inspect := by
    rintro l _ rfl
    rcases cases_visible l with rfl | ⟨a, rfl⟩ | ⟨R, event, k, rfl⟩
    · exact .diverged _
    · change Layer _ _ _ _ (pure a) (mapBody plan (pure a))
      rw [map_pure]
      cases a with
      | inl b => exact .exit (.refl _)
      | inr p =>
        apply Layer.edge (rightPending := aligned plan p)
        · rcases forward_cases plan instr source checked p with same | hop
          · rw [Sum.map_inr, same]
            exact .refl _
          · apply Silent.more
            rw [hop]
            exact .refl _
        · rfl
    · rw [map_vis]
      exact .request event (.refl _) (fun _ => rfl)

private def Reverse (r : Right (E := E) (W := W) (J := J) (α := α))
    (l : Left (E := E) (V := V) (K := K) (α := α)) : Prop :=
  r = mapBody plan l ∨ ∃ p, r = pure (.inr (aligned plan p)) ∧ l = pure (.inr p)

private def backwardSimulation (checked : plan.hasBackedge source = true) :
    Simulation instr instr (plan.rewrite source) source where
  boundary r l := r = aligned plan l
  residual := Reverse plan
  atBoundary := by
    rintro _ l rfl
    exact Or.inl (step_aligned plan instr source l)
  inspect := by
    rintro r l (rfl | ⟨p, rfl, rfl⟩)
    · rcases cases_visible l with rfl | ⟨a, rfl⟩ | ⟨R, event, k, rfl⟩
      · rw [map_diverge]
        exact .diverged _
      · change Layer _ _ _ _ (mapBody plan (pure a)) (pure a)
        rw [map_pure]
        cases a with
        | inl b => exact .exit (.refl _)
        | inr p =>
          rcases forward_cases plan instr source checked p with same | hop
          · rw [Sum.map_inr, same]
            exact .edge (.refl _) rfl
          · apply Layer.leftTransfer (.refl _)
            rw [hop]
            exact Or.inr ⟨p, rfl, rfl⟩
      · rw [map_vis]
        exact .request event (.refl _) (fun _ => Or.inl rfl)
    · exact .edge (.refl _) rfl

def buildWitness {target : Graph W J F} (checked : Checked plan source target) :
    Witness plan instr source target := by
  obtain rfl := checked.rewritten
  exact
    { forward := forwardSimulation plan instr source checked.backedge
      backward := backwardSimulation plan instr source checked.backedge
      enterForward := entry_routed plan instr source
      enterBackward := fun store => by
        rw [entry_routed]
        exact Or.inl rfl }

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split
