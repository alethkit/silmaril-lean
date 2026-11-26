module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Defs
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Feedback
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Feedback
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Liveness.Demand.Wiring

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Proofs

open OrderedRuntime.Structured (Ty Opcode)
open OrderedState.Partial (Path)
open ExplicitRuntime.Partial (Observation wireModel kindAbnormal abnormalAt abnormal)
open NestedTheta.Partial (exec kindExec tagged)
open Liveness.Demand.Proofs (ScopeAgrees valueAt read_all read_selected gamma_read_agrees
  scope_snoc scope_at_entry)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable (m : ExplicitRuntime.Partial.Model.{u,v,w} P E σ)

private theorem tagged_agrees {carried : Ports (Ty V)}
    (exit : Demand) (live : Feedback.Mask carried.length)
    {again : Bool} {left : Tuple (wireModel m).Val carried}
    {right : Tuple (wireModel m).Val (Theta.BodyResults carried)}
    (related : (Feedback.bodyDemand exit live).Agrees (tagged (wireModel m) again left) right) :
    ∃ next, tagged (wireModel m) again next = right ∧
      Feedback.Agrees live left next ∧ exit.Agrees left next := by
  cases right with
  | cons tag next =>
    refine ⟨next, congrArg (fun flag => Tuple.cons flag next) (related .head rfl), ?_, ?_⟩
    · intro ty p needed
      apply related (.tail p)
      cases ty with
      | state => rfl
      | value | control => exact Bool.or_eq_true_iff.2 (Or.inr needed)
    · intro ty p needed
      apply related (.tail p)
      cases ty with
      | state => rfl
      | value | control => exact Bool.or_eq_true_iff.2 (Or.inl needed)

private theorem node_matches (path : Path)
    {ins out : Ports (Ty V)} (kind : Kind (Opcode P E) ins out) (wires : Wires args past ins)
    {childSigs : Fin kind.arity → List (Ports (Ty V))}
    (children : ∀ j, Term (Opcode P E) kind.entry [] (childSigs j) kind.exit)
    (childMatches : ∀ j (demand : Demand) (l r : Tuple (wireModel m).Val kind.entry),
      ScopeAgrees (scope := []) ((children j).demandPlan demand).live l r PUnit.unit PUnit.unit →
        Matches demand.Agrees (exec (wireModel m) (children j) l PUnit.unit)
          (exec (wireModel m) (children j) r PUnit.unit)
          (abnormalAt m (path ++ [(past.length, j.val)]) (children j) l PUnit.unit)
          (abnormalAt m (path ++ [(past.length, j.val)]) (children j) r PUnit.unit))
    (next : List Address) (left right : Tuple (wireModel m).Val args)
    (localsL localsR : Locals (wireModel m).Val past)
    (agree : ScopeAgrees (kind.demandReads past.length next wires
      (fun j request => ((children j).demandPlan request).live)) left right localsL localsR) :
    let run := fun j input => exec (wireModel m) (children j) input PUnit.unit
    let bad := fun j input => abnormalAt m (path ++ [(past.length, j.val)]) (children j) input PUnit.unit
    let demand : Demand := fun p => next.contains (.output past.length p)
    Matches demand.Agrees
      (kindExec (wireModel m) kind run (wires.read left localsL))
      (kindExec (wireModel m) kind run (wires.read right localsR))
      (kindAbnormal m path past.length kind run bad (wires.read left localsL))
      (kindAbnormal m path past.length kind run bad (wires.read right localsR)) := by
  intro run bad demand
  cases kind with
  | base shape =>
    cases shape with
    | simple =>
      rw [read_all wires agree]
      exact ⟨fun h => ⟨_, h, fun _ _ => rfl⟩, id⟩
    | gamma extra =>
      cases wires with
      | cons selector captures =>
        let tagL : ULift (Fin (extra + 2)) := valueAt (F := (wireModel m).Val) selector left localsL
        let tagR : ULift (Fin (extra + 2)) := valueAt (F := (wireModel m).Val) selector right localsR
        obtain ⟨sameTag, related⟩ := gamma_read_agrees selector captures
          (fun j => ((children j).demandPlan demand).live) agree
        have sameTag : tagL = tagR := sameTag
        change Matches demand.Agrees
          (run tagL.down (Wires.read captures left localsL))
          (run tagR.down (Wires.read captures right localsR))
          (bad tagL.down (Wires.read captures left localsL))
          (bad tagR.down (Wires.read captures right localsR))
        rw [← sameTag]
        exact childMatches tagL.down demand _ _ (related tagL.down)
  | theta =>
    let body := children (0 : Fin 1)
    let live := body.feedbackLive demand
    let request := Feedback.bodyDemand demand live
    have inputs : Feedback.Agrees live (wires.read left localsL) (wires.read right localsR) :=
      fun p needed => read_selected (fun _ i => Feedback.includes live i) wires agree p needed
    have matchesBody {l r : Tuple (wireModel m).Val _} (related : Feedback.Agrees live l r) :
        Matches request.Agrees (run (0 : Fin 1) l) (run (0 : Fin 1) r)
          (bad (0 : Fin 1) l) (bad (0 : Fin 1) r) := by
      apply childMatches (0 : Fin 1) request
      intro ty source needed
      cases source with
      | output i _ => exact i.elim0
      | arg p => exact related p ((Feedback.Proofs.includes_live_iff body demand p).2 needed)
    refine theta_matches m (Feedback.Agrees live) demand.Agrees
      (fun x again y => run (0 : Fin 1) x (tagged (wireModel m) again y)) (bad (0 : Fin 1))
      ?_ (fun related stopped => (matchesBody related).abnormal stopped) inputs
    intro l r after again related finished
    obtain ⟨packet, returned, observation⟩ := (matchesBody related).returns finished
    obtain ⟨next, eq, feedback, exit⟩ := tagged_agrees m demand live observation
    exact ⟨next, eq.symm ▸ returned, feedback, exit⟩

private theorem term_matches (path : Path) (term : Term (Opcode P E) args past sigs outs)
    (demand : Demand) (left right : Tuple (wireModel m).Val args)
    (localsL localsR : Locals (wireModel m).Val past)
    (agree : ScopeAgrees (term.demandPlan demand).live left right localsL localsR) :
    Matches demand.Agrees (exec (wireModel m) term left localsL) (exec (wireModel m) term right localsR)
      (abnormalAt m path term left localsL) (abnormalAt m path term right localsR) := by
  induction term generalizing path demand with
  | ret wires =>
    constructor
    · intro output returned
      change wires.read left localsL = output at returned
      subst output
      exact ⟨wires.read right localsR, rfl, fun p needed =>
        read_selected demand.observes wires
          (fun source h => agree source (List.mem_append_left _ h)) p needed⟩
    · intro obs impossible
      exact False.elim impossible
  | @bind _ head _ past _ node children rest ihChild ihRest =>
    let next := (rest.demandPlan demand).live
    let requested : Demand := fun p => next.contains (.output past.length p)
    have current := node_matches m path node.kind node.inputs children
      (fun j wanted l r h => ihChild j (path ++ [(past.length, j.val)]) wanted l r PUnit.unit PUnit.unit h)
      next left right localsL localsR (fun source h => agree source (List.mem_append_left _ h))
    have resume {outL outR : Tuple (wireModel m).Val head} (matched : requested.Agrees outL outR) :
        ScopeAgrees next left right (localsL.snoc outL) (localsR.snoc outR) := by
      apply scope_snoc (fun source h => agree source (List.mem_append_right _ h))
      intro ty p live
      apply matched p
      cases ty with
      | state => rfl
      | value | control => exact List.contains_iff_mem.2 live
    constructor
    · rintro output ⟨middle, finished, later⟩
      obtain ⟨other, finished', related⟩ := current.returns finished
      obtain ⟨result, later', matched⟩ := (ihRest path demand left right _ _ (resume related)).returns later
      exact ⟨result, ⟨other, finished', later'⟩, matched⟩
    · intro obs endpoint
      rcases endpoint with failed | ⟨middle, finished, later⟩
      · exact Or.inl (current.abnormal failed)
      · obtain ⟨other, finished', related⟩ := current.returns finished
        exact Or.inr ⟨other, finished', (ihRest path demand left right _ _ (resume related)).abnormal later⟩

private theorem graph_matches (g : Graph (Opcode P E) args [] sigs outs) (demand : Demand)
    (left right : Tuple (wireModel m).Val args) (agree : g.AgreesOnDemandInputs demand left right) :
    Matches demand.Agrees (NestedTheta.Partial.returns (wireModel m) g left)
      (NestedTheta.Partial.returns (wireModel m) g right) (abnormal m g left) (abnormal m g right) :=
  term_matches m [] g.toTerm demand left right PUnit.unit PUnit.unit (scope_at_entry g demand agree)

theorem returnsDemand_iff (g : Graph (Opcode P E) args [] sigs outs) (demand : Demand)
    (left right : Tuple (wireModel m).Val args) (agree : g.AgreesOnDemandInputs demand left right)
    (expected : Tuple (wireModel m).Val outs) :
    ReturnsDemand m g demand left expected ↔ ReturnsDemand m g demand right expected := by
  have transfer {l r : Tuple (wireModel m).Val args} (agree : g.AgreesOnDemandInputs demand l r)
      (h : ReturnsDemand m g demand l expected) : ReturnsDemand m g demand r expected := by
    obtain ⟨out, returned, sameOutput⟩ := h
    obtain ⟨other, returned', related⟩ := (graph_matches m g demand l r agree).returns returned
    exact ⟨other, returned', fun p needed => (related p needed).symm.trans (sameOutput p needed)⟩
  exact ⟨transfer agree, transfer (fun p needed => (agree p needed).symm)⟩

theorem abnormal_iff (g : Graph (Opcode P E) args [] sigs outs) (demand : Demand)
    (left right : Tuple (wireModel m).Val args) (agree : g.AgreesOnDemandInputs demand left right)
    (obs : Observation m) :
    abnormal m g left obs ↔ abnormal m g right obs :=
  ⟨(graph_matches m g demand left right agree).abnormal,
    (graph_matches m g demand right left (fun p live => (agree p live).symm)).abnormal⟩

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Partial.Proofs
