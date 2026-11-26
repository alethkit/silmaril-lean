module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Proofs

open Silmaril.Semantics.Dataflow

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem plan_live (t : Term Op args past sigs outs) (demand : Demand) :
    (t.demandPlan demand).live = sweep (t.demandPlan demand).reads past.length := by
  induction t with
  | ret => rfl
  | bind node children rest _ ih =>
    simp only [Term.demandPlan, DemandPlan.prepend, sweep, ih, List.length_append,
      List.length_cons, List.length_nil]

theorem mem_liveIn_iff (g : Graph Op args [] sigs outs) (demand : Demand) (a : Address) :
    a ∈ g.demandLiveIn demand ↔ a ∈ (g.demandLiveness demand).mayOut 0 := by
  simpa only [Graph.demandLiveIn, List.mem_eraseDups, plan_live, List.length_nil,
    Graph.demandLiveness, List.drop_zero] using mem_sweep_iff (g.toTerm.demandPlan demand).reads 0 a

section Wiring

variable {Ty : Type u} {F : Ty → Type w}
variable {entry users : Ports Ty} {scope : List (Ports Ty)}

private def valueAt {ty : Ty} (source : Origin entry scope ty)
    (input : Tuple F entry) (locals : Locals F scope) : F ty :=
  match source with
  | .arg p => input.get p
  | .output i p => (locals.get i).get p

private def ScopeAgrees (live : List Address) (left right : Tuple F entry)
    (localsL localsR : Locals F scope) : Prop :=
  ∀ {ty} (source : Origin entry scope ty), source.address ∈ live →
    valueAt source left localsL = valueAt source right localsR

private theorem get_read (wires : Wires entry scope users) (input : Tuple F entry)
    (locals : Locals F scope) {ty : Ty} (p : Port users ty) :
    (wires.read input locals).get p = valueAt (wires.get p) input locals := by
  induction p with
  | head => cases wires with | cons wire _ => cases wire <;> rfl
  | tail p ih => cases wires with | cons _ rest => exact ih rest

private theorem get_selected (selected : Ty → Nat → Bool) (wires : Wires entry scope users)
    {ty : Ty} (p : Port users ty) (needed : selected ty p.index = true) :
    (wires.get p).address ∈ selectWires selected wires := by
  induction p generalizing selected with
  | head =>
    cases wires with
    | cons source rest =>
      simp only [Port.index] at needed
      simp [selectWires, Tuple.get, needed]
  | tail p ih =>
    cases wires with
    | cons source rest =>
      exact List.mem_append_right _ (ih (fun t i => selected t (i + 1)) rest needed)

private theorem read_all (wires : Wires entry scope users) {left right : Tuple F entry}
    {localsL localsR : Locals F scope} (agree : ScopeAgrees wires.addresses left right localsL localsR) :
    wires.read left localsL = wires.read right localsR := by
  induction wires with
  | nil => rfl
  | cons source rest ih =>
    exact congrArg₂ Tuple.cons (agree source (List.mem_cons_self ..))
      (ih fun next h => agree next (List.mem_cons_of_mem _ h))

private theorem locals_snoc_agree {head : Ports Ty}
    (left right : Locals F scope) (nextL nextR : Tuple F head)
    (keep : Nat → Nat → Prop)
    (old : ∀ (i : Fin scope.length) {ty} (p : Port scope[i] ty), keep i.val p.index →
      (left.get i).get p = (right.get i).get p)
    (new : ∀ {ty} (p : Port head ty), keep scope.length p.index → nextL.get p = nextR.get p) :
    ∀ (i : Fin (scope ++ [head]).length) {ty} (p : Port (scope ++ [head])[i] ty), keep i.val p.index →
      ((left.snoc nextL).get i).get p = ((right.snoc nextR).get i).get p := by
  induction scope generalizing keep with
  | nil => exact fun i => Fin.cases (fun p h => new p h) (fun j => j.elim0) i
  | cons sig rest ih =>
    intro i
    refine Fin.cases (fun p h => old 0 p h) (fun j p h => ?_) i
    exact ih left.2 right.2 (fun k p => keep (k + 1) p)
      (fun k {_} p h => old k.succ p h) new j p h

private theorem scope_snoc {head : Ports Ty} {live : List Address} {left right : Tuple F entry}
    {localsL localsR : Locals F scope} {nextL nextR : Tuple F head}
    (old : ScopeAgrees (live.filter (fun a => !definedAt scope.length a)) left right localsL localsR)
    (new : ∀ {ty} (p : Port head ty), .output scope.length p.index ∈ live → nextL.get p = nextR.get p) :
    ScopeAgrees live left right (localsL.snoc nextL) (localsR.snoc nextR) := by
  intro ty source needed
  cases source with
  | arg p => exact old (.arg p) (by simpa [Origin.address, definedAt] using needed)
  | output i p =>
    apply locals_snoc_agree localsL localsR nextL nextR (fun n k => .output n k ∈ live) _ new i p needed
    intro j _ q needed
    exact old (.output j q) (by
      simp [Origin.address, definedAt, needed, Nat.ne_of_lt j.isLt])

end Wiring

private theorem result_refl (demand : Demand) {F : PortType V S → Type w}
    (result : Option (Tuple F outs)) : demand.ResultAgrees result result := by
  cases result with
  | none => exact .none
  | some => exact .some (fun _ _ => rfl)

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
    rw [read_all wires agree]
    exact result_refl _ _
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
          have edge := get_selected (fun _ i => ((List.ofFn armLive).flatten).contains (.arg i))
            captures p (List.contains_iff_mem.2 joined)
          exact (get_read (F := m.Val) captures left localsL p).trans
            ((agree (captures.get p) (List.mem_cons_of_mem _ edge)).trans
              (get_read (F := m.Val) captures right localsR p).symm)

private theorem eval_agrees (m : Model.{u, v, w} Op) (fuel : Nat)
    (term : Term Op args past sigs outs) (demand : Demand)
    (left right : Tuple m.Val args) (localsL localsR : Locals m.Val past)
    (agree : ScopeAgrees (term.demandPlan demand).live left right localsL localsR) :
    demand.ResultAgrees (term.eval m fuel left localsL) (term.eval m fuel right localsR) := by
  induction term generalizing demand with
  | ret wires =>
    apply Demand.ResultAgrees.some
    intro ty p needed
    have edge := get_selected demand.observes wires p needed
    simpa only [get_read] using
      (agree (wires.get p) (List.mem_append_left _ edge))
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
  apply eval_agrees
  intro ty source live
  cases source with
  | output i _ => exact i.elim0
  | arg p => exact agree p ((mem_liveIn_iff g demand _).1 (List.mem_eraseDups.2 live))

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
