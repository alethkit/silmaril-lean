module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Proofs

open Silmaril.Semantics.Dataflow

private theorem step_iff (reads : List (List Address)) (x : Nat → Set Address)
    (pc : Nat) (a : Address) :
    a ∈ (problem reads).mayEquations.step x pc ↔
      a ∈ (reads.drop pc).headD [] ∨ (a ∈ x (pc + 1) ∧ definedAt pc a = false) := by
  simp [Equations.step_apply, Equations.join, problem, GenKill.mayEquations, or_comm]

private theorem drop_next {α : Type*} (rows : List α) (pc : Nat) :
    rows.drop (pc + 1) = (rows.drop pc).tail := by
  rw [← List.drop_drop, List.drop_one]

theorem sweep_iff (reads : List (List Address)) (pc : Nat) (a : Address) :
    a ∈ sweep (reads.drop pc) pc ↔ a ∈ (problem reads).mayOut pc := by
  have lower : ∀ suffix n, reads.drop n = suffix →
      ∀ address, address ∈ sweep suffix n → address ∈ (problem reads).mayOut n := by
    intro suffix
    induction suffix with
    | nil => simp [sweep]
    | cons row rest ih =>
      intro n h address ha
      have stable := congrFun (problem reads).mayEquations.least_isSolution n
      change (problem reads).mayEquations.step (problem reads).mayOut n =
        (problem reads).mayOut n at stable
      rw [← stable, step_iff, h]
      simp only [sweep, transfer, List.mem_append, List.mem_filter, Bool.not_eq_true'] at ha
      exact ha.imp id fun ⟨live, preserved⟩ =>
        ⟨ih (n + 1) (by simp [drop_next, h]) address live, preserved⟩
  have safe : (problem reads).mayEquations.IsSafe
      (fun n => {address | address ∈ sweep (reads.drop n) n}) := by
    intro n address h
    rw [step_iff] at h
    change address ∈ sweep (reads.drop n) n
    cases dropped : reads.drop n with
    | nil => simp [drop_next, dropped, sweep] at h
    | cons row rest =>
      simpa [drop_next, dropped, sweep, transfer] using h
  exact ⟨lower _ pc rfl a, fun h => (problem reads).mayEquations.least_le_of_isSafe safe pc h⟩

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem liveAt_iff (g : Graph Op args [] sigs outs) (pc : Nat) (a : Address) :
    a ∈ g.liveAt pc ↔ a ∈ g.liveness.mayOut pc := by
  simpa [Graph.liveAt, Graph.liveness] using sweep_iff g.toTerm.readSchedule pc a

private theorem read_congr {Ty : Type u} {F : Ty → Type w} {entry users : Ports Ty}
    {scope : List (Ports Ty)} (wires : Wires entry scope users)
    (left right : Tuple F entry) (locals : Locals F scope)
    (agree : ∀ {ty} (p : Port entry ty), .arg p.index ∈ wires.addresses →
      left.get p = right.get p) :
    wires.read left locals = wires.read right locals := by
  induction wires with
  | nil => rfl
  | cons source rest ih =>
    have tail := ih (fun p hp => agree p (List.mem_cons_of_mem _ hp))
    change Tuple.cons _ (Wires.read rest left locals) = Tuple.cons _ (Wires.read rest right locals)
    rw [tail]
    cases source with
    | output => rfl
    | arg p =>
      exact congrArg (fun value => Tuple.cons value (Wires.read rest right locals))
        (agree p (by simp [Wires.addresses, Origin.address]))

private theorem eval_congr (m : Model.{u, v, w} Op) (fuel : Nat)
    (t : Term Op args past sigs outs) (pc : Nat)
    (left right : Tuple m.Val args) (locals : Locals m.Val past)
    (agree : ∀ {ty} (p : Port args ty), .arg p.index ∈ sweep t.readSchedule pc →
      left.get p = right.get p) :
    t.eval m fuel left locals = t.eval m fuel right locals := by
  induction t generalizing pc with
  | ret wires =>
    exact congrArg some (read_congr wires left right locals fun p hp =>
      agree p (by simpa [Term.readSchedule, sweep, transfer] using hp))
  | bind node children rest _ ih =>
    have inputs := read_congr node.inputs left right locals fun p hp =>
      agree p (by simpa only [Term.readSchedule, sweep, transfer, List.mem_append] using Or.inl hp)
    simp only [Term.eval, inputs]
    congr 1
    funext result
    apply ih (pc + 1)
    intro ty p hp
    exact agree p (by simp [Term.readSchedule, sweep, transfer, definedAt, hp])

theorem run_congr (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (left right : Tuple m.Val args) (agree : g.AgreesOnLiveInputs left right) :
    g.run m fuel left = g.run m fuel right := by
  rw [← g.run_toTerm m fuel left, ← g.run_toTerm m fuel right]
  exact eval_congr m fuel g.toTerm 0 left right PUnit.unit fun p hp =>
    agree p ((sweep_iff g.toTerm.readSchedule 0 _).1 hp)

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Proofs
