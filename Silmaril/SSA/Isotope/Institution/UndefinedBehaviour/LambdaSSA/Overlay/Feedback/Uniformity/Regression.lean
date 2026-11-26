module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Uniformity.Thms

/-! Forward simulation and exact local observations on the source's reachable
points allow the target to add an edge to UB or to a replaying block. -/

open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

namespace LambdaSSAFeedbackUniformityRegression

private abbrev R : List Unit := [()]
private abbrev L : List Unit := []
private abbrev start : Point R.length Unit Unit := .entry ()
private abbrev stopped : Point R.length Unit Unit := .block 0 .unit ()
private abbrev extra : Point R.length Unit Unit := .block 0 (.inl .unit) ()
private abbrev Local := Behaviour (R ++ L).length Unit Unit

private abbrev jump (a : Value Unit) : Outcome (R ++ L).length Unit Unit :=
  .ret (internal R L 0) a ()

private def source : Run R L Unit Unit
  | .entry _ => ↑({o | o = jump .unit} : Set (Outcome (R ++ L).length Unit Unit))
  | .block .. => ↑(∅ : Set (Outcome (R ++ L).length Unit Unit))

private noncomputable def target (tail : Local) : Run R L Unit Unit := by
  classical
  exact fun
    | .entry _ => ↑({o | o = jump .unit ∨ o = jump (.inl .unit)} : Set (Outcome (R ++ L).length Unit Unit))
    | .block _ a _ => if a = .inl .unit then tail else ↑(∅ : Set (Outcome (R ++ L).length Unit Unit))

private theorem source_edge {p q : Point R.length Unit Unit} (h : Step (R := R) (L := L) source p q) :
    p = start ∧ q = stopped := by
  cases h with
  | @branch i a s ret =>
    cases p with
    | entry state =>
      have eq : Outcome.ret (internal R L i) a s = jump .unit := ret.2
      obtain ⟨_, rfl, rfl⟩ := Outcome.ret.inj eq
      cases state
      exact ⟨rfl, congrArg (fun i => Point.block i .unit ()) (Fin.eq_zero i)⟩
    | block _ _ _ => exact ret.2.elim

private theorem source_reachable {p : Point R.length Unit Unit} (h : Reaches source start p) :
    p = start ∨ p = stopped := by
  cases h with
  | refl => exact Or.inl rfl
  | tail _ edge => exact Or.inr (source_edge edge).2

private theorem external_ne_jump (o : Outcome L.length Unit Unit) (a : Value Unit) :
    external R L o ≠ jump a := by
  cases o with
  | ret i _ _ => exact Fin.elim0 i
  | fault _ | diverge => intro h; cases h

/-- The identity map is a nonvacuous forward simulation with exact local
top tags and final observations on every reached source point. -/
theorem one_way (tail : Local) :
    (∀ p q, Step source p q → Step (target tail) p q) ∧
      (∀ p, Reaches source start p →
        (source p = ⊤ ↔ target tail p = ⊤) ∧
          ∀ o, (source p).Ordinary (external R L o) ↔ (target tail p).Ordinary (external R L o)) := by
  constructor
  · intro p q h
    obtain ⟨rfl, rfl⟩ := source_edge h
    exact .branch ⟨WithTop.coe_ne_top, Or.inl rfl⟩
  · intro p reached
    rcases source_reachable reached with rfl | rfl
    · refine ⟨iff_of_false WithTop.coe_ne_top WithTop.coe_ne_top, fun o => ?_⟩
      exact iff_of_false (fun h => external_ne_jump o _ h.2)
        (fun h => h.2.elim (external_ne_jump o _) (external_ne_jump o _))
    · have h : target tail stopped = source stopped := by
        simp [target, source]
      rw [h]
      exact ⟨Iff.rfl, fun _ => Iff.rfl⟩

private theorem source_safe : ¬ ReachesUB source start := by
  rintro ⟨p, _, top⟩
  cases p <;> exact WithTop.coe_ne_top top

private theorem source_no_divergence : ¬ (close source start).Ordinary .diverge := by
  intro div
  rcases (ordinary_close_iff.mp div).2 with ⟨p, reached, localDiv⟩ | ⟨_, path, _, steps⟩
  · rcases source_reachable reached with rfl | rfl
    · exact external_ne_jump .diverge _ localDiv.2
    · exact localDiv.2
  · have eq := (source_edge (steps 0)).2.symm.trans (source_edge (steps 1)).1
    cases eq

private theorem extra_edge (tail : Local) : Step (target tail) start extra :=
  .branch ⟨WithTop.coe_ne_top, Or.inr rfl⟩

theorem one_way_loses_ub : close source start ≠ ⊤ ∧ close (target ⊤) start = ⊤ := by
  refine ⟨fun h => source_safe (close_eq_top_iff.mp h), close_eq_top_iff.mpr ?_⟩
  exact ⟨extra, .single (extra_edge ⊤), by simp [target]⟩

private def replay : Local := ↑({o | o = jump (.inl .unit)} : Set (Outcome (R ++ L).length Unit Unit))

theorem one_way_loses_divergence :
    ¬ (close source start).Ordinary .diverge ∧ (close (target replay) start).Ordinary .diverge := by
  refine ⟨source_no_divergence, ordinary_close_iff.mpr ⟨?_, Or.inr ⟨rfl, ?_⟩⟩⟩
  · rintro ⟨p, _, top⟩
    cases p with
    | entry _ => exact WithTop.coe_ne_top top
    | block i a s =>
      classical
      by_cases eq : a = .inl .unit <;> simp [target, replay, eq] at top
  · have stays : target replay extra = replay := by simp [target]
    have replayEdge : Step (target replay) extra extra :=
      .branch (stays.symm ▸ (show replay.Ordinary (jump (.inl .unit)) from ⟨WithTop.coe_ne_top, rfl⟩))
    let path : Nat → Point R.length Unit Unit
      | 0 => start
      | _ + 1 => extra
    exact ⟨path, rfl, fun n => Nat.casesOn n (extra_edge replay) (fun _ => replayEdge)⟩

#print axioms close_eq_iff
#print axioms Bisimulation.close_eq
#print axioms Bisimulation.infinite_iff
#print axioms close_relabel
#print axioms close_slide
#print axioms denote_feedback_uniform
#print axioms one_way
#print axioms one_way_loses_ub
#print axioms one_way_loses_divergence

end LambdaSSAFeedbackUniformityRegression
