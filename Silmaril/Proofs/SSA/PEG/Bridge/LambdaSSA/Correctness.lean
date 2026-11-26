module

public import Silmaril.SSA.PEG.Bridge.LambdaSSA.Defs
import Silmaril.Proofs.SSA.PEG.Bridge.LambdaSSA.Source
public import Silmaril.SSA.SeaOfNodes.Diamond.Arms.LambdaSSA.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.LambdaSSA.Proofs

open RVSDG (Port Tuple Origin Wires Locals extend)
open Silmaril.SSA.SeaOfNodes
open Simple (Code select emitValue)
open Target

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params before after ins results : List (Ty Data)} {t : Ty Data}
variable {past : List (List (Diamond.Ty (Ty Data)))}

variable (m : TotalModel P) (input : Tuple m.toPEG.Value params)

private theorem pack_unpack (xs : Tuple (ValueAt m) (ports results)) :
    pack (F := ValueAt m) (unpack (F := ValueAt m) results xs) = xs := by
  induction results with
  | nil => cases xs; rfl
  | cons t ts ih => cases xs; simp only [pack, unpack, ih]

private theorem pack_get (p : Port before t) (xs : Tuple m.toPEG.Value before) :
    (pack (F := ValueAt m) xs).get (dataPort p) = xs.get p := by
  induction p with
  | head => cases xs; rfl
  | tail p ih => cases xs with | cons _ xs => exact ih xs

private theorem collect_some {F : Ty Data → Type} (xs : Tuple F ins) :
    collect ins (fun slot => some (xs.get (portAt ins slot))) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change (match some x, collect _ (fun i => some (xs.get (portAt _ i))) with
      | some x, some xs => some (Tuple.cons x xs)
      | _, _ => none) = some (Tuple.cons x xs)
    rw [ih]

private theorem some_map_injective {F : Ty Data → Type} (a b : Tuple F results)
    (eq : a.map (fun _ => some) = b.map (fun _ => some)) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys =>
      simp only [Tuple.map, Tuple.cons.injEq, Option.some.injEq] at eq
      exact congrArg₂ Tuple.cons eq.1 (ih _ eq.2)

private theorem read_newest {out : Target.ValueSort Data}
    (locals : Locals (ValueAt m) past) (value : Diamond.sortValue (model m).value out) :
    Diamond.read (model m) (newest past out) (entry m input)
      (locals.snoc (.cons value .nil)) = value := by
  induction past with
  | nil => rfl
  | cons head tail ih => exact ih locals.2

private theorem read_weaken {head : List (Diamond.Ty (Ty Data))} {out : Diamond.Ty (Ty Data)}
    (locals : Locals (ValueAt m) past) (value : Tuple (ValueAt m) head) (wire : Origin (ports params) past out) :
    Diamond.read (model m) (weaken head wire) (entry m input) (locals.snoc value) =
      Diamond.read (model m) wire (entry m input) locals := by
  cases wire with
  | arg => rfl
  | output i p =>
    induction past with
    | nil => exact i.elim0
    | cons a rest ih =>
      refine Fin.cases (motive := fun j => ∀ (q : Port (a :: rest)[j] out),
        Diamond.read (model m) (weaken head (.output (past := a :: rest) j q)) (entry m input) (locals.snoc value) =
          Diamond.read (model m) (.output (past := a :: rest) j q) (entry m input) locals) ?_ ?_ i p
      · intro q
        rfl
      · intro j q
        exact ih locals.2 j q

private abbrev Agrees (scope : Scope params before past) (locals : Locals (ValueAt m) past)
    (values : Values m.toPEG before) : Prop :=
  ∀ {t} (p : Port before t),
    values.get p = some (Diamond.read (model m) (scope p) (entry m input) locals)

private theorem agrees_push (scope : Scope params before past) (locals : Locals (ValueAt m) past)
    (values : Values m.toPEG before) (agree : Agrees m input scope locals values)
    (v : m.toPEG.Value t) :
    Agrees m input scope.push (locals.snoc (.cons v .nil)) (.cons (some v) values) := by
  intro slot p
  cases p with
  | head => exact congrArg some (read_newest m input locals (out := .data t) v).symm
  | tail p => exact (agree p).trans (congrArg some (read_weaken m input locals _ (scope p)).symm)

private theorem read_wires (scope : Scope params before past)
    (locals : Locals (ValueAt m) past) (values : Values m.toPEG before)
    (agree : Agrees m input scope locals values) (refs : Tuple (Port before) results) :
    select values refs =
      (unpack (F := ValueAt m) results (Wires.read (scope.wires refs) (entry m input) locals)).map
        (fun _ => some) := by
  induction refs with
  | nil => rfl
  | cons p refs ih => exact congrArg₂ Tuple.cons (agree p) ih

private theorem emit_agrees (scope : Scope params before past) (locals : Locals (ValueAt m) past)
    (values : Values m.toPEG before) (agree : Agrees m input scope locals values)
    (label : Label P params (Fin 0) ins t) (refs : Tuple (Port before) ins) :
    let op := lowerLabel label (scope.wires refs)
    emitValue m.toPEG input label refs values = some
      ((model m).run (.data op.2.1) (Wires.read op.2.2 (entry m input) locals)) := by
  let xs : Tuple m.toPEG.Value ins := unpack (F := ValueAt m) ins (Wires.read (scope.wires refs) (entry m input) locals)
  have reads (i : Fin ins.length) :
      values.get (refs.get (portAt ins i)) = some (xs.get (portAt ins i)) := by
    have h : select values refs = xs.map (fun _ => some) :=
      read_wires m input scope locals values agree refs
    have same := congrArg (fun vs : Values m.toPEG ins => vs.get (portAt ins i)) h
    simpa only [select, get_map] using same
  cases label with
  | param p =>
    exact congrArg some (pack_get m p input).symm
  | op op =>
    change (collect ins (fun i => values.get (refs.get (portAt ins i)))).elim none
      (fun args => some (m.run op args)) = some (m.run op xs)
    rw [funext reads, collect_some]
    rfl
  | phi =>
    let ts : List (Ty Data) := [.bool, t, t]
    change (values.get (refs.get (portAt ts 0))).elim none
      (fun b => if b.down then values.get (refs.get (portAt ts 1)) else values.get (refs.get (portAt ts 2))) =
        some (Operation.eval m .select xs)
    rw [reads 0, reads 1, reads 2]
    generalize xs = args
    cases args with
    | cons flag rest =>
      cases rest with
      | cons left rest =>
        cases rest with
        | cons right rest =>
          cases rest
          change (if flag.down then some left else some right) =
            some (if flag.down then left else right)
          split <;> rfl
  | theta l | eval l | pass l => exact l.elim0

private theorem schedule_agrees {F : _ → Type} (code : Code P params before after)
    (src : Values m.toPEG before) (scope : Scope params before past)
    (locals : Locals (ValueAt m) past) (agree : Agrees m input scope locals src)
    (next : ∀ past', Scope params after past' → Schedule P params past' F)
    (observe : ∀ {past'}, F past' → Locals (ValueAt m) past' → Prop)
    (finish : ∀ past' (scope' : Scope params after past') (locals' : Locals (ValueAt m) past'),
      Agrees m input scope' locals' (code.eval m.toPEG input src) →
      observe (next past' scope').result ((next past' scope').flow.eval (model m) (entry m input) locals')) :
    let plan := schedule code scope next
    observe plan.result (plan.flow.eval (model m) (entry m input) locals) := by
  induction code with
  | empty =>
    dsimp only
    rw [schedule]
    exact finish past scope locals agree
  | @emit nodes args result prior label refs ih =>
    dsimp only
    rw [schedule]
    apply ih _
    intro past' scope' locals' agree'
    let op := lowerLabel label (scope'.wires refs)
    let v := (model m).run (.data op.2.1) (Wires.read op.2.2 (entry m input) locals')
    have extended : Agrees m input scope'.push (locals'.snoc (.cons v .nil))
        (.cons (some v) (prior.eval m.toPEG input src)) :=
      agrees_push (t := result) m input scope' locals' _ agree' v
    have emitted : emitValue m.toPEG input label refs (prior.eval m.toPEG input src) = some v :=
      emit_agrees m input scope' locals' _ agree' label refs
    apply finish _ scope'.push (locals'.snoc (.cons v .nil))
    intro slot p
    change (Tuple.cons (F := fun t => Option (m.toPEG.Value t))
      (emitValue m.toPEG input label refs (prior.eval m.toPEG input src))
      (prior.eval m.toPEG input src)).get p = _
    rw [emitted]
    exact extended p

private theorem arm_agrees (a : Arm P params before results) (scope : Scope params before past)
    (locals : Locals (ValueAt m) past) (values : Values m.toPEG before)
    (agree : Agrees m input scope locals values) :
    select (a.code.eval m.toPEG input values) a.outputs =
      (unpack (F := ValueAt m) results ((arm a scope).eval (model m) (entry m input) locals)).map
        (fun _ => some) := by
  refine schedule_agrees (F := fun endPast => Wires (ports params) endPast (ports results))
    m input a.code values scope locals agree
    (fun _ layout => ⟨[], .nil, layout.wires a.outputs⟩)
    (fun out final => select (a.code.eval m.toPEG input values) a.outputs =
      (unpack (F := ValueAt m) results (out.read (entry m input) final)).map (fun _ => some)) ?_
  intro _ layout final matched
  exact read_wires m input layout final _ matched a.outputs

private theorem shared_agrees (g : ScopedDiamond P params results) :
    let plan := scheduleShared g
    let final := plan.flow.eval (model m) (entry m input) PUnit.unit
    let values := g.sharedCode.eval m.toPEG input .nil
    values.get g.guard = some (Diamond.read (model m) plan.result.1 (entry m input) final) ∧
      Agrees m input plan.result.2 final values := by
  refine schedule_agrees (past := [])
    (F := fun endPast => Origin (ports params) endPast (.value .predicate) × Scope params g.shared endPast)
    m input g.sharedCode .nil (fun p => nomatch p) PUnit.unit
    (fun p => nomatch p) _
    (fun out final =>
      (g.sharedCode.eval m.toPEG input .nil).get g.guard =
        some (Diamond.read (model m) out.1 (entry m input) final) ∧
        Agrees m input out.2 final (g.sharedCode.eval m.toPEG input .nil)) ?_
  intro past' scope locals agree
  let flag := Diamond.read (model m) (scope g.guard) (entry m input) locals
  exact ⟨(agree g.guard).trans (congrArg some (read_newest m input locals (out := .predicate) flag).symm),
    fun p => (agree p).trans (congrArg some (read_weaken (head := [.value .predicate]) m input locals
      (.cons flag .nil) (scope p)).symm)⟩

/-- Both arms consume only the shared context. The chosen PEG packet and the
existing diamond's selected predecessor packet agree position by position. -/
theorem observe_lower (g : ScopedDiamond P params results) (wf : WellFounded g.toPEG.Demand)
    (idx : Index 0) :
    g.toPEG.observe m.toPEG (g.toPEG.denote m.toPEG input wf) idx =
      (unpack (F := ValueAt m) results ((graph g).denote (model m) (entry m input))).map (fun _ => some) := by
  let plan := scheduleShared g
  let final := plan.flow.eval (model m) (entry m input) PUnit.unit
  let flag := Diamond.read (model m) plan.result.1 (entry m input) final
  obtain ⟨test, capture⟩ := shared_agrees m input g
  rw [observe_source m.toPEG input g wf idx flag test]
  unfold Diamond.Arms.Graph.denote
  change (if flag.down then _ else _) =
    (unpack (F := ValueAt m) results (((graph g).arms ((graph g).merge.slot
      (Diamond.Projection.ofBool flag.down))).eval (model m) (entry m input) final)).map (fun _ => some)
  cases b : flag.down
  · exact arm_agrees m input g.onFalse plan.result.2 final _ capture
  · exact arm_agrees m input g.onTrue plan.result.2 final _ capture

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA

universe u

/-- Characterize all finite target returns, including the external exit and
the unchanged ambient state, using the guarded PEG observation. -/
theorem lower_eval_iff {σ : Type u} (g : ScopedDiamond P params results)
    (wf : WellFounded g.toPEG.Demand) (idx : Index 0)
    (start finish : σ) (label : Nat) (payload : Value (Diamond.LambdaSSA.Atom (model m))) :
    Semantics.Region.Eval (Diamond.LambdaSSA.instruction (model m))
      (Diamond.LambdaSSA.inputEnv (model m) (entry m input)) g.lower start label payload finish ↔
      label = 0 ∧ finish = start ∧ ∃ result : Tuple m.toPEG.Value results,
        g.toPEG.observe m.toPEG (g.toPEG.denote m.toPEG input wf) idx = result.map (fun _ => some) ∧
        payload = Diamond.LambdaSSA.encodeTuple (model m) (pack (F := ValueAt m) result) := by
  unfold ScopedDiamond.lower
  rw [Diamond.Arms.LambdaSSA.lower_eval_iff, observe_lower m input g wf idx]
  let out := (graph g).denote (model m) (entry m input)
  change (_ ∧ payload = Diamond.LambdaSSA.encodeTuple (model m) out ∧ _) ↔
    (_ ∧ _ ∧ ∃ result : Tuple m.toPEG.Value results,
      (unpack (F := ValueAt m) results out).map (fun _ => some) = result.map (fun _ => some) ∧ _)
  constructor
  · rintro ⟨exit, value, state⟩
    refine ⟨exit, state, unpack (F := ValueAt m) results out, rfl, ?_⟩
    rw [pack_unpack]
    exact value
  · rintro ⟨exit, state, result, observed, value⟩
    have same := some_map_injective _ _ observed
    rw [← same, pack_unpack] at value
    exact ⟨exit, value, state⟩

end Silmaril.SSA.PEG.Bridge.LambdaSSA.Proofs
