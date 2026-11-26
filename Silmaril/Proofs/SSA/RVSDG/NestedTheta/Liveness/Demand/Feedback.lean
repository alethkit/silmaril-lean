module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
import Silmaril.Semantics.Dataflow.Iteration
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Powerset

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Feedback.Proofs

open Silmaril.Semantics.Dataflow

abbrev DemandLE (left right : Demand) : Prop :=
  ∀ i, left i = true → right i = true

universe u v

private theorem port_bound {Ty : Type u} {ports : Ports Ty} {t : Ty} (p : Port ports t) :
    p.index < ports.length := by
  induction p with
  | head => simp [Port.index]
  | tail p ih => exact Nat.succ_lt_succ ih

private theorem includes_port_iff {Ty : Type u} {ports : Ports Ty} {t : Ty}
    (p : Port ports t) (live : Mask ports.length) :
    includes live p.index = true ↔ (⟨p.index, port_bound p⟩ : Fin ports.length) ∈ live := by
  simp [includes, port_bound p]

private theorem includes_mono {arity : Nat} {small large : Mask arity} (h : small ⊆ large) :
    DemandLE (includes small) (includes large) := by
  intro p needed
  by_cases valid : p < arity
  · simp only [includes, dite_eq_left valid, decide_eq_true_eq] at needed ⊢
    exact h needed
  · simp [includes, valid] at needed

private theorem bodyDemand_mono {arity : Nat} {left right : Demand} {small large : Mask arity}
    (exit : DemandLE left right) (feedback : small ⊆ large) :
    DemandLE (bodyDemand left small) (bodyDemand right large) := by
  intro i needed
  cases i with
  | zero => rfl
  | succ i =>
    simp only [bodyDemand, Bool.or_eq_true] at needed ⊢
    exact needed.imp (exit i) (includes_mono feedback i)

private theorem step_mono {arity : Nat} {left right : Demand} (exit : DemandLE left right)
    (body : Demand → List Address)
    (mono : ∀ {a b}, DemandLE a b → body a ⊆ body b)
    {small large : Mask arity} (feedback : small ⊆ large) :
    step left body small ⊆ step right body large := by
  intro p needed
  simp only [step, Finset.mem_filter, Finset.mem_univ, true_and] at needed ⊢
  exact mono (bodyDemand_mono exit feedback) needed

private theorem close_mono {arity : Nat} {left right : Demand} (exit : DemandLE left right)
    (body : Demand → List Address)
    (mono : ∀ {a b}, DemandLE a b → body a ⊆ body b) :
    (close left body : Mask arity) ⊆ close right body :=
  Monotone.iterate_le_of_le (f := step left body)
    (fun _ _ h => step_mono (fun _ h => h) body mono h)
    (fun _ => step_mono exit body mono le_rfl) arity ∅

theorem selectWires_mono {Ty : Type u} {args users : Ports Ty} {past : List (Ports Ty)}
    (wires : Wires args past users) {low high : Ty → Nat → Bool}
    (more : ∀ t, DemandLE (low t) (high t)) :
    selectWires low wires ⊆ selectWires high wires := by
  induction wires generalizing low high with
  | nil => exact fun _ h => h
  | @cons t _ source rest ih =>
    intro address present
    simp only [selectWires, List.mem_append] at present ⊢
    refine present.imp ?_ (fun h => ih (fun ty i h => more ty (i + 1) h) h)
    intro active
    by_cases h : low t 0 = true
    · simpa only [ite_eq_left (more t 0 h)] using (show address ∈ [source.address] from by
        simpa only [ite_eq_left h] using active)
    · simp [h] at active

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem reads_mono {ins out : Ports (PortType V S)} (kind : Kind Op ins out)
    (wires : Wires args past ins) (pc : Nat) {small large : List Address} (next : small ⊆ large)
    (body : Fin kind.arity → Demand → List Address)
    (mono : ∀ i {a b}, DemandLE a b → body i a ⊆ body i b) :
    kind.demandReads pc small wires body ⊆ kind.demandReads pc large wires body := by
  have exit : DemandLE (fun p => small.contains (.output pc p))
      (fun p => large.contains (.output pc p)) :=
    fun _ active => List.contains_iff_mem.2 (next (List.contains_iff_mem.1 active))
  cases kind with
  | theta =>
    apply selectWires_mono wires
    intro _
    exact includes_mono (close_mono exit (body (0 : Fin 1)) (mono (0 : Fin 1)))
  | base shape =>
    cases shape with
    | simple => exact fun _ h => h
    | gamma =>
      cases wires with
      | cons selector captures =>
        apply List.cons_subset_cons
        apply selectWires_mono captures
        intro _ p live
        apply List.contains_iff_mem.2
        obtain ⟨arm, enumerated, needs⟩ := List.mem_flatten.1 (List.contains_iff_mem.1 live)
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 enumerated
        exact List.mem_flatten.2 ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, mono i exit needs⟩

private theorem plan_mono (t : Term Op args past sigs outs) {low high : Demand} (more : DemandLE low high) :
    (t.demandPlan low).live ⊆ (t.demandPlan high).live := by
  induction t generalizing low high with
  | ret wires =>
    simp only [Term.demandPlan, DemandPlan.prepend, transfer, List.filter_nil, List.append_nil]
    apply selectWires_mono wires
    intro ty i h
    cases ty with
    | state => rfl
    | control | value => exact more i h
  | bind node children rest ihChild ihRest =>
    have suffix := ihRest more
    intro address live
    simp only [Term.demandPlan, DemandPlan.prepend, transfer, List.mem_append, List.mem_filter] at live ⊢
    exact live.imp (fun h => reads_mono node.kind node.inputs _ suffix _
      (fun i _ _ demand => ihChild i demand) h) (fun h => ⟨suffix h.1, h.2⟩)

private theorem iterate_fixed_at_arity {arity : Nat} (f : Mask arity → Mask arity)
    (mono : Monotone f) : f (f^[arity] ∅) = f^[arity] ∅ := by
  let x : Nat → Mask arity := fun k => f^[k] ∅
  have next (k : Nat) : f (x k) = x (k + 1) := (Function.iterate_succ_apply' f k ∅).symm
  have chain : Monotone x := Monotone.monotone_iterate_of_le_map mono (Finset.empty_subset _)
  have strict_card (k : Nat) (hne : x k ≠ x (k + 1)) : (x k).card < (x (k + 1)).card :=
    Finset.card_lt_card (lt_of_le_of_ne (chain (Nat.le_succ k)) hne)
  have growth (k : Nat) (hne : x k ≠ x (k + 1)) : k + 1 ≤ (x (k + 1)).card := by
    induction k with
    | zero =>
      have inc := strict_card 0 hne
      omega
    | succ k ih =>
      have earlier : x k ≠ x (k + 1) := fun eq =>
        hne ((next k).symm.trans ((congrArg f eq).trans (next (k + 1))))
      have bound := ih earlier
      have inc := strict_card (k + 1) hne
      omega
  by_contra h
  have lower := growth arity (fun eq => h ((next arity).trans eq.symm))
  have upper := (x (arity + 1)).card_le_univ
  rw [Fintype.card_fin] at upper
  omega

attribute [local instance] Fintype.toCompleteLattice

/-- The native solver's bound and leastness apply to any monotone body summary. -/
theorem close_isLeast {arity : Nat} (exit : Demand) (body : Demand → List Address)
    (mono : ∀ {a b}, DemandLE a b → body a ⊆ body b) :
    IsLeast {live : Mask arity | step exit body live = live} (close exit body) := by
  let f : Mask arity →o Mask arity :=
    ⟨step exit body, fun _ _ h => step_mono (fun _ h => h) body mono h⟩
  have fixed : f (f^[arity] ⊥) = f^[arity] ⊥ := iterate_fixed_at_arity f f.monotone
  have least : close exit body = f.lfp := iterate_eq_lfp_of_isFixedPt f fixed
  rw [least]
  exact f.isLeast_lfp

theorem includes_close_iff {Ty : Type u} {carried : Ports Ty} {ty : Ty} (p : Port carried ty)
    (exit : Demand) (body : Demand → List Address)
    (mono : ∀ {a b}, DemandLE a b → body a ⊆ body b) :
    includes (close (arity := carried.length) exit body) p.index = true ↔
      Address.arg p.index ∈ body (bodyDemand exit (close (arity := carried.length) exit body)) := by
  let live : Mask carried.length := close exit body
  have fixed : step exit body live = live := (close_isLeast exit body mono).1
  have selected :
      (⟨p.index, port_bound p⟩ : Fin carried.length) ∈ step exit body live ↔
        Address.arg p.index ∈ body (bodyDemand exit live) := by
    simp only [step, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [fixed] at selected
  exact (includes_port_iff p live).trans selected

theorem feedback_isLeast {carried : Ports (PortType V S)}
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (exit : Demand) :
    IsLeast {live | step exit (fun demand => (body.demandPlan demand).live) live = live}
      (body.feedbackLive exit) :=
  close_isLeast exit _ (plan_mono body)

theorem includes_live_iff {carried : Ports (PortType V S)}
    (body : Term Op carried [] sigs (Theta.BodyResults carried)) (exit : Demand)
    {ty : PortType V S} (p : Port carried ty) :
    includes (body.feedbackLive exit) p.index = true ↔
      Address.arg p.index ∈ (body.demandPlan (bodyDemand exit (body.feedbackLive exit))).live :=
  includes_close_iff p exit _ (plan_mono body)

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Feedback.Proofs
