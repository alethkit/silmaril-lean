module

public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Liveness.Thms

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

@[expose] def valueAt {ty : Ty} (source : Origin entry scope ty)
    (input : Tuple F entry) (locals : Locals F scope) : F ty :=
  match source with
  | .arg p => input.get p
  | .output i p => (locals.get i).get p

@[expose] def ScopeAgrees (live : List Address) (left right : Tuple F entry)
    (localsL localsR : Locals F scope) : Prop :=
  ∀ {ty} (source : Origin entry scope ty), source.address ∈ live →
    valueAt source left localsL = valueAt source right localsR

theorem get_read (wires : Wires entry scope users) (input : Tuple F entry)
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

theorem read_selected (selected : Ty → Nat → Bool) (wires : Wires entry scope users)
    {left right : Tuple F entry} {localsL localsR : Locals F scope}
    (agree : ScopeAgrees (selectWires selected wires) left right localsL localsR)
    {ty : Ty} (p : Port users ty) (needed : selected ty p.index = true) :
    (wires.read left localsL).get p = (wires.read right localsR).get p :=
  (get_read wires left localsL p).trans
    ((agree (wires.get p) (get_selected selected wires p needed)).trans
      (get_read wires right localsR p).symm)

theorem read_all (wires : Wires entry scope users) {left right : Tuple F entry}
    {localsL localsR : Locals F scope} (agree : ScopeAgrees wires.addresses left right localsL localsR) :
    wires.read left localsL = wires.read right localsR := by
  induction wires with
  | nil => rfl
  | cons source rest ih =>
    exact congrArg₂ Tuple.cons (agree source (List.mem_cons_self ..))
      (ih fun next h => agree next (List.mem_cons_of_mem _ h))

/-- The γ transfer retains the selector and supplies each arm with agreement
on its own live capture ports. -/
theorem gamma_read_agrees {tagTy : Ty} {arity : Nat}
    (selector : Origin entry scope tagTy) (captures : Wires entry scope users)
    (armLive : Fin arity → List Address) {left right : Tuple F entry}
    {localsL localsR : Locals F scope}
    (agree : ScopeAgrees (selector.address ::
      selectWires (fun _ i => (List.ofFn armLive).flatten.contains (.arg i)) captures)
      left right localsL localsR) :
    valueAt selector left localsL = valueAt selector right localsR ∧
    ∀ i, ScopeAgrees (scope := []) (armLive i)
      (captures.read left localsL) (captures.read right localsR) PUnit.unit PUnit.unit := by
  refine ⟨agree selector (List.mem_cons_self ..), ?_⟩
  intro i ty source live
  cases source with
  | output j _ => exact j.elim0
  | arg p =>
    have joined : Address.arg p.index ∈ (List.ofFn armLive).flatten :=
      List.mem_flatten.2 ⟨armLive i, List.mem_ofFn.2 ⟨i, rfl⟩, live⟩
    exact read_selected (fun _ j => (List.ofFn armLive).flatten.contains (.arg j))
      captures (fun edge h => agree edge (List.mem_cons_of_mem _ h)) p
      (List.contains_iff_mem.2 joined)

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

theorem scope_snoc {head : Ports Ty} {live : List Address} {left right : Tuple F entry}
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

/-- The shared solution supplies the entry case of the scoped wire invariant. -/
theorem scope_at_entry (g : Graph Op args [] sigs outs) (demand : Demand)
    {F : PortType V S → Type w} {left right : Tuple F args}
    (agree : g.AgreesOnDemandInputs demand left right) :
    ScopeAgrees (scope := []) (g.toTerm.demandPlan demand).live left right PUnit.unit PUnit.unit := by
  intro ty source live
  cases source with
  | output i _ => exact i.elim0
  | arg p => exact agree p ((mem_liveIn_iff g demand _).1 (List.mem_eraseDups.2 live))

end Silmaril.SSA.RVSDG.NestedTheta.Liveness.Demand.Proofs
