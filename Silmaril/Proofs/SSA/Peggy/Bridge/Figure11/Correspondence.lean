module

public import Silmaril.SSA.Peggy.Bridge.Figure11.Defs
public import Silmaril.SSA.Peggy.Bridge.Egg.Defs
import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.SSA.Peggy.Bridge.Egg.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.Bridge.Figure11

open Silmaril.SSA
open Silmaril.SSA.Peggy
open RVSDG (Tuple Port)
open Silmaril.SSA.Peggy.Acyclic (Ranked)
open Silmaril.SSA.Peggy.Bridge.Figure11
open Silmaril.Logic.Egg

variable {Data : Type} {P : PEG.InstructionSet.{0,0} Data}
variable {params results : List (PEG.Ty Data)} {n n' : Nat}
variable {g : PEG.Graph P params results n 0} {g' : PEG.Graph P params results n' 0}
variable (m : PEG.Interpretation.{0,0,0} P)

theorem demandWellFounded (r : Ranked g) : WellFounded g.Demand := by
  apply Subrelation.wf _ (InvImage.wf (fun q : PEG.Request n 0 => r.rank q.1) Nat.lt_wfRel.wf)
  rintro ⟨b, j⟩ ⟨a, i⟩ ⟨_, ⟨slot, _, rfl⟩, _⟩
  exact r.decreases a slot

private theorem lift_cast {s t : PEG.Ty Data} (h : s = t) (v : (toAcyclic m).Partial s) :
    liftPartial m (h ▸ v : (toAcyclic m).Partial t) =
      (h ▸ liftPartial m v : Option (m.Value t)) := by
  cases h
  rfl

private theorem lift_inputs {ts : List (PEG.Ty Data)} (env : Tuple m.Value ts)
    {t : PEG.Ty Data} (p : Port ts t) :
    (Acyclic.Interpretation.portIndex_sort p ▸
      liftPartial m (toInputs m env (Acyclic.Interpretation.portIndex p)) : Option (m.Value t)) =
      some (env.get p) := by
  induction p with
  | head =>
    cases env with
    | cons x xs =>
      change some ((valueEquiv m.carrier _) ((valueEquiv m.carrier _).symm x)) = some x
      rw [Equiv.apply_symm_apply]
  | tail p ih => cases env; exact ih _

private theorem collect_lift {ts : List (PEG.Ty Data)}
    (args : ∀ i : Fin ts.length, (toAcyclic m).Partial ts[i]) :
    PEG.collect ts (fun i => liftPartial m (args i)) =
      ((toAcyclic m).definedArgs args).map (Tuple.map fun t => valueEquiv m.carrier t) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [PEG.collect, Acyclic.Interpretation.definedArgs, ih]
    cases head : args 0 <;> cases tail : (toAcyclic m).definedArgs (fun i => args i.succ) <;> rfl

private theorem lift_evalLabel (env : Tuple m.Value params)
    {ts : List (PEG.Ty Data)} {t : PEG.Ty Data} (label : PEG.Label P params (Fin 0) ts t)
    (args : ∀ i : Fin ts.length, (toAcyclic m).Partial ts[i]) (idx : PEG.Index 0) :
    liftPartial m ((toAcyclic m).evalLabel (toInputs m env) label args) =
      label.interpret m env idx (fun slot _ _ => liftPartial m (args slot)) := by
  cases label with
  | param p =>
    simp only [Acyclic.Interpretation.evalLabel, PEG.Label.interpret, lift_cast]
    exact lift_inputs m env p
  | op instr =>
    simp only [Acyclic.Interpretation.evalLabel, Acyclic.Interpretation.applyPrim,
      PEG.Label.interpret, collect_lift]
    cases (toAcyclic m).definedArgs args with
    | none => rfl
    | some vals =>
      change liftPartial m ((toAcyclic m).prim instr vals) =
        m.run instr (vals.map fun t => valueEquiv m.carrier t)
      simp [toAcyclic, liftPartial, Option.map_map, Function.comp_def]
  | phi =>
    change liftPartial m ((toAcyclic m).applyPhi args) = _
    let control : Option Bool := args 0
    change liftPartial m (control.bind fun flag => if flag then args 1 else args 2) =
      (liftPartial m (t := .bool) control).elim none fun flag => if flag.down then
        liftPartial m (args 1) else liftPartial m (args 2)
    cases control with
    | none => rfl
    | some flag => cases flag <;> rfl
  | theta l | eval l | pass l => exact l.elim0

theorem valuation_solves (r : Ranked g) (env : Tuple m.Value params) :
    g.Solves m env (valuation r m env) := by
  rintro ⟨i, idx⟩
  unfold valuation Ranked.eval
  rw [Ranked.fold, lift_evalLabel]
  simp only [PEG.Graph.equation, PEG.Graph.demandStep, PEG.Ref.read]
  apply congrArg (PEG.Label.interpret m env idx (g.node i).label)
  funext slot j legal
  exact lift_cast m ((g.node i).arg slot).typed _

theorem denote_eq_valuation (r : Ranked g) (env : Tuple m.Value params)
    (wf : WellFounded g.Demand) : g.denote m env wf = valuation r m env :=
  g.solves_unique m env wf (g.denote_solves m env wf) (valuation_solves m r env)

private theorem get_map {S : Type} {F G : S → Type} {ts : List S} {t : S}
    (f : ∀ s, F s → G s) (xs : Tuple F ts) (p : Port ts t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem tuple_eq {F : PEG.Ty Data → Type} {ts : List (PEG.Ty Data)} (xs ys : Tuple F ts)
    (h : ∀ i : Fin ts.length, xs.get (PEG.portAt ts i) = ys.get (PEG.portAt ts i)) :
    xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => exact congrArg₂ Tuple.cons (h 0) (ih ys (fun i => h i.succ))

theorem observe_get (r : Ranked g) (env : Tuple m.Value params) (wf : WellFounded g.Demand)
    (idx : PEG.Index 0) (i : Fin results.length) :
    (g.observe m (g.denote m env wf) idx).get (PEG.portAt results i) =
      liftPartial m (r.evalOutputs (toAcyclic m) (toInputs m env) i) := by
  rw [denote_eq_valuation m r env wf]
  simp only [PEG.Graph.observe, get_map, PEG.Ref.read, valuation, Ranked.evalOutputs, lift_cast]

open Silmaril.SSA.Peggy.Bridge.Egg in
theorem checkOutputs_figure11_sound [DecidableEq Data] (eqPrim : PrimitiveEq P)
    {rs : List (Core.Rule (signature P))} {r : Ranked g} {r' : Ranked g'}
    {receipts : ∀ i : Fin results.length, Core.Replay.Receipt rs (context params) results[i]}
    (accepted : (checkOutputs eqPrim r r' receipts).isSome)
    (hrules : ∀ rule ∈ rs, rule.Holds (model (toAcyclic m)))
    (env : Tuple m.Value params) (wf : WellFounded g.Demand) (wf' : WellFounded g'.Demand)
    (idx : PEG.Index 0) :
    g.observe m (g.denote m env wf) idx = g'.observe m (g'.denote m env wf') idx := by
  have h := checkOutputs_sound eqPrim accepted (toAcyclic m) hrules (toInputs m env)
  apply tuple_eq
  intro i
  rw [observe_get m r, observe_get m r', congrFun h i]

end Silmaril.Proofs.SSA.Peggy.Bridge.Figure11
