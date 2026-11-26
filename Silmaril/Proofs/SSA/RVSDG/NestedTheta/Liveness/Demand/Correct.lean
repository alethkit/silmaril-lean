module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Feedback
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Proofs

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem result_refl (demand : Demand) {F : PortType V S → Type w}
    (result : Option (Tuple F outs)) : demand.ResultAgrees result result := by
  cases result with
  | none => exact .none
  | some => exact .some (fun _ _ => rfl)

/-- Each successful body step agrees on the continue flag. A restart uses
the same live-input relation on the new carried tuples. -/
private theorem iterate_agrees {F : PortType V S → Type w} {carried : Ports (PortType V S)}
    (exit : Demand) (live : Feedback.Mask carried.length)
    (body : Tuple F carried → Option (Tuple F (Theta.BodyResults carried)))
    (branch : F (.control 2) → Bool)
    (step_agrees : ∀ left right, Feedback.Agrees live left right →
      (Feedback.bodyDemand exit live).ResultAgrees (body left) (body right))
    (fuel : Nat) (left right : Tuple F carried) (agree : Feedback.Agrees live left right) :
    exit.ResultAgrees (iterate body branch fuel left) (iterate body branch fuel right) := by
  induction fuel generalizing left right with
  | zero => exact .none
  | succ fuel ih =>
    have related := step_agrees left right agree
    simp only [iterate]
    generalize body left = stepL at related ⊢
    generalize body right = stepR at related ⊢
    cases related with
    | none => exact .none
    | @some packetL packetR related =>
      cases packetL with | cons flagL nextL =>
        cases packetR with | cons flagR nextR =>
          have decision : flagL = flagR := related .head rfl
          rw [decision]
          by_cases again : branch flagR = true
          · simp only [ite_eq_left again]
            apply ih
            intro ty p needed
            apply related (.tail p)
            cases ty with
            | state => rfl
            | value | control => exact Bool.or_eq_true_iff.2 (Or.inr needed)
          · simp only [ite_eq_right again]
            apply Demand.ResultAgrees.some
            intro ty p needed
            apply related (.tail p)
            cases ty with
            | state => rfl
            | value | control => exact Bool.or_eq_true_iff.2 (Or.inl needed)

private theorem kind_agrees (m : Model.{u, v, w} Op) (fuel : Nat)
    {ins out : Ports (PortType V S)} (kind : Kind Op ins out) (wires : Wires args past ins)
    {childSigs : Fin kind.arity → List (Ports (PortType V S))}
    (children : ∀ i, Term Op kind.entry [] (childSigs i) kind.exit)
    (child_agrees : ∀ i (requested : Demand) (left right : Tuple m.Val kind.entry),
      ScopeAgrees (scope := []) ((children i).demandPlan requested).live
        left right PUnit.unit PUnit.unit →
      requested.ResultAgrees ((children i).run m fuel left) ((children i).run m fuel right))
    (next : List Address) (left right : Tuple m.Val args) (localsL localsR : Locals m.Val past)
    (agree : ScopeAgrees (kind.demandReads past.length next wires
      (fun i requested => ((children i).demandPlan requested).live)) left right localsL localsR) :
    let requested : Demand := fun p => next.contains (.output past.length p)
    requested.ResultAgrees
      (kind.eval m fuel (fun i entry => (children i).run m fuel entry) (wires.read left localsL))
      (kind.eval m fuel (fun i entry => (children i).run m fuel entry) (wires.read right localsR)) := by
  cases kind with
  | theta =>
    let exit : Demand := fun p => next.contains (.output past.length p)
    let body := children (0 : Fin 1)
    let live := body.feedbackLive exit
    have inputs : Feedback.Agrees live (wires.read left localsL) (wires.read right localsR) :=
      fun p needed => read_selected (fun _ i => Feedback.includes live i) wires agree p needed
    apply iterate_agrees exit live (body.run m fuel) _ _ fuel _ _ inputs
    intro inputL inputR related
    apply child_agrees (0 : Fin 1)
    intro ty source needed
    cases source with
    | output i _ => exact i.elim0
    | arg p => exact related p ((Feedback.Proofs.includes_live_iff body exit p).2 needed)
  | base shape =>
    cases shape with
    | simple =>
      rw [read_all wires agree]
      exact result_refl _ _
    | gamma extra =>
      cases wires with
      | cons selector captures =>
        let requested : Demand := fun p => next.contains (.output past.length p)
        let tagL : ULift (Fin (extra + 2)) := valueAt (F := m.Val) selector left localsL
        let tagR : ULift (Fin (extra + 2)) := valueAt (F := m.Val) selector right localsR
        have sameTag : tagL = tagR := agree selector (List.mem_cons_self ..)
        change requested.ResultAgrees
          ((children tagL.down).run m fuel (Wires.read captures left localsL))
          ((children tagR.down).run m fuel (Wires.read captures right localsR))
        rw [← sameTag]
        apply child_agrees
        intro ty source live
        cases source with
        | output i _ => exact i.elim0
        | arg p =>
          let armLive := fun i => ((children i).demandPlan requested).live
          have joined : Address.arg p.index ∈ (List.ofFn armLive).flatten :=
            List.mem_flatten.2 ⟨armLive tagL.down, List.mem_ofFn.2 ⟨tagL.down, rfl⟩, live⟩
          exact read_selected (fun _ i => ((List.ofFn armLive).flatten).contains (.arg i))
            captures (fun edge h => agree edge (List.mem_cons_of_mem _ h)) p
            (List.contains_iff_mem.2 joined)

private theorem eval_agrees (m : Model.{u, v, w} Op) (fuel : Nat)
    (term : Term Op args past sigs outs) (demand : Demand)
    (left right : Tuple m.Val args) (localsL localsR : Locals m.Val past)
    (agree : ScopeAgrees (term.demandPlan demand).live left right localsL localsR) :
    demand.ResultAgrees (term.eval m fuel left localsL) (term.eval m fuel right localsR) := by
  induction term generalizing demand with
  | ret wires =>
    apply Demand.ResultAgrees.some
    intro ty p needed
    exact read_selected demand.observes wires
      (fun source h => agree source (List.mem_append_left _ h)) p needed
  | @bind _ head _ past _ node children rest ihChild ihRest =>
    let next := (rest.demandPlan demand).live
    have gen := fun {ty} (source : Origin _ past ty) hp =>
      agree source (List.mem_append_left _ hp)
    have preserved : ScopeAgrees (next.filter (fun a => !definedAt past.length a))
        left right localsL localsR := fun source hp => agree source (List.mem_append_right _ hp)
    have first := kind_agrees m fuel node.kind node.inputs children
      (fun i requested l r h => ihChild i requested l r PUnit.unit PUnit.unit h)
      next left right localsL localsR gen
    change demand.ResultAgrees
      ((node.kind.eval m fuel (fun i entry => (children i).run m fuel entry)
        (node.inputs.read left localsL)).bind (fun result => rest.eval m fuel left (localsL.snoc result)))
      ((node.kind.eval m fuel (fun i entry => (children i).run m fuel entry)
        (node.inputs.read right localsR)).bind (fun result => rest.eval m fuel right (localsR.snoc result)))
    generalize node.kind.eval m fuel (fun i entry => (children i).run m fuel entry)
      (node.inputs.read left localsL) = resultL at first ⊢
    generalize node.kind.eval m fuel (fun i entry => (children i).run m fuel entry)
      (node.inputs.read right localsR) = resultR at first ⊢
    cases first with
    | none => exact .none
    | some related =>
      apply ihRest demand
      apply scope_snoc preserved
      intro ty p needed
      have selected : Demand.observes (fun i => next.contains (.output past.length i)) ty p.index = true := by
        cases ty with
        | state => rfl
        | value | control => exact List.contains_iff_mem.2 needed
      exact related p selected

theorem run_agrees (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op) (fuel : Nat)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right) :
    demand.ResultAgrees (g.run m fuel left) (g.run m fuel right) := by
  rw [← g.run_toTerm m fuel left, ← g.run_toTerm m fuel right]
  exact eval_agrees m fuel g.toTerm demand left right PUnit.unit PUnit.unit
    (scope_at_entry g demand agree)

private theorem observation_iff {F : PortType V S → Type w} {demand : Demand}
    {left right : Option (Tuple F outs)} (agree : demand.ResultAgrees left right)
    (expected : Tuple F outs) :
    (∃ out, left = some out ∧ demand.Agrees out expected) ↔
    (∃ out, right = some out ∧ demand.Agrees out expected) := by
  cases agree with
  | none => rfl
  | some matchPorts =>
    constructor
    · rintro ⟨_, eq, related⟩
      cases eq
      exact ⟨_, rfl, fun p hp => (matchPorts p hp).symm.trans (related p hp)⟩
    · rintro ⟨_, eq, related⟩
      cases eq
      exact ⟨_, rfl, fun p hp => (matchPorts p hp).trans (related p hp)⟩

theorem returns_agree (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right)
    (expected : Tuple m.Val outs) :
    g.ReturnsDemand m demand left expected ↔ g.ReturnsDemand m demand right expected := by
  have observe (input : Tuple m.Val args) :
      g.ReturnsDemand m demand input expected ↔
        ∃ fuel out, g.run m fuel input = some out ∧ demand.Agrees out expected :=
    ⟨fun ⟨out, ⟨fuel, run⟩, h⟩ => ⟨fuel, out, run, h⟩,
      fun ⟨fuel, out, run, h⟩ => ⟨out, ⟨fuel, run⟩, h⟩⟩
  rw [observe left, observe right]
  exact exists_congr fun fuel => observation_iff (run_agrees g m fuel demand left right agree) expected

theorem hasFiniteReturn_iff (g : Graph Op args [] sigs outs) (m : Model.{u, v, w} Op)
    (demand : Demand) (left right : Tuple m.Val args) (agree : g.AgreesOnDemandInputs demand left right) :
    (∃ out, g.Returns m left out) ↔ ∃ out, g.Returns m right out := by
  have observed (entry : Tuple m.Val args) :
      (∃ out, g.Returns m entry out) ↔ ∃ expected, g.ReturnsDemand m demand entry expected :=
    ⟨fun ⟨out, h⟩ => ⟨out, out, h, fun _ _ => rfl⟩, fun ⟨_, out, h, _⟩ => ⟨out, h⟩⟩
  rw [observed left, observed right]
  exact exists_congr (returns_agree g m demand left right agree)

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Proofs
