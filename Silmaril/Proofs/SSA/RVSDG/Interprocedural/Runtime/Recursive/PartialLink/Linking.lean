module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Defs
public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.Continuation.Partial.Thms

public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Proofs

open Continuation.Partial (Primitives Eval Site Config Step)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {primitives : Primitives m σ}
variable {args outs : Ports (Ty V S)} {past sigs : List (Ports (Ty V S))}

private theorem eval_exists (term : RVSDG.Term Op args past sigs outs)
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) (store : σ) :
    ∃ outcome, Eval primitives (.region (embed term) inputs locals) store outcome := by
  induction term generalizing store with
  | ret wires => exact ⟨_, .ret wires inputs locals store⟩
  | bind node children rest childIH restIH =>
    cases node with
    | mk ins shape wires cs =>
      cases shape with
      | simple opcode =>
        let site : Site m := ⟨_, _, opcode, cs, fun i => embed (children i), wires.read inputs locals⟩
        rcases _root_.Part.eq_none_or_eq_some ((primitives.step opcode site.input).run store) with
          absent | ⟨⟨values, middle⟩, found⟩
        · exact ⟨_, .bindBlocked (.primitiveBlocked site store absent)⟩
        · have first : Eval primitives site.job store (.returned values middle) :=
            .primitive site (found.symm ▸ _root_.Part.mem_some _)
          obtain ⟨outcome, more⟩ := restIH inputs (locals.snoc values) middle
          exact ⟨outcome, .bind first more⟩
      | gamma extra =>
        cases read : wires.read inputs locals with
        | cons tag entry =>
          cases tag with
          | control tag =>
            obtain ⟨first, evaluation⟩ := childIH tag entry PUnit.unit store
            cases first with
            | returned values middle =>
              obtain ⟨outcome, more⟩ := restIH inputs (locals.snoc values) middle
              refine ⟨outcome, .bind ?_ more⟩
              exact read.symm ▸ .gamma evaluation
            | blocked site pending stopped =>
              refine ⟨_, .bindBlocked (site := site) (pending := pending) (stopped := stopped) ?_⟩
              exact read.symm ▸ .gamma evaluation

private theorem embedded_returns (term : RVSDG.Term Op args past sigs outs)
    (inputs : Tuple m.Val args) (locals : Locals m.Val past) :
    Returns m (.region (embed term) inputs locals) (evalInitializer m term inputs locals) := by
  induction term with
  | ret wires => exact .ret wires inputs locals
  | bind node children rest childIH restIH =>
    cases node with
    | mk ins shape wires cs =>
      cases shape with
      | simple opcode =>
        exact .bind (.primitive opcode cs (fun i => embed (children i)) (wires.read inputs locals))
          (restIH inputs (locals.snoc (m.primitive opcode (wires.read inputs locals))))
      | gamma extra =>
        cases read : wires.read inputs locals with
        | cons tag entry =>
          cases tag with
          | control tag =>
            rw [evalInitializer, read]
            exact .bind (read.symm ▸ .gamma (childIH tag entry PUnit.unit))
              (restIH inputs (locals.snoc (evalInitializer m (children tag) entry PUnit.unit)))

private def observe (unitId vertex : Nat) (config : Config m σ outs) : Option (Outcome m σ outs) :=
  match config.result with
  | some (values, store) => some (.linked values store)
  | none => (Continuation.Partial.selectedPrimitive config.control).map fun active =>
    .undefined ⟨unitId, vertex, active.site, config.store⟩

private def observation (unitId vertex : Nat) (outcome : Continuation.Partial.Outcome m σ outs) :
    Outcome m σ outs :=
  match outcome with
  | .returned values store => .linked values store
  | .blocked site _ store => .undefined ⟨unitId, vertex, site, store⟩

private theorem observe_halt (unitId vertex : Nat) (outcome : Continuation.Partial.Outcome m σ outs) :
    observe unitId vertex (outcome.atStack .halt) = some (observation unitId vertex outcome) := by
  cases outcome with
  | returned => rfl
  | blocked site => cases site; rfl

private theorem terminal {job : Job m outs} {store : σ}
    {outcome : Continuation.Partial.Outcome m σ outs} (evaluation : Eval primitives job store outcome)
    {next : Config m σ outs} : ¬ Step primitives (outcome.atStack .halt) next := by
  cases outcome with
  | returned =>
    intro edge
    exact _root_.Part.notMem_none _ edge
  | blocked =>
    exact (evaluation.blocks .halt).no_step

private theorem eval_observation_unique {job : Job m outs} {store : σ}
    {left right : Continuation.Partial.Outcome m σ outs} (unitId vertex : Nat)
    (first : Eval primitives job store left) (second : Eval primitives job store right) :
    observation unitId vertex left = observation unitId vertex right := by
  have same : left.atStack .halt = right.atStack .halt := by
    have unique : Relator.RightUnique (Step (final := outs) primitives) :=
      fun _ _ _ ab ac => _root_.Part.mem_unique ab ac
    rcases (first.steps .halt).total_of_right_unique unique (second.steps .halt) with path | path
    · rcases path.cases_head with equal | ⟨_, edge, _⟩
      · exact equal
      · exact False.elim (terminal first edge)
    · rcases path.cases_head with equal | ⟨_, edge, _⟩
      · exact equal.symm
      · exact False.elim (terminal second edge)
  exact Option.some.inj ((observe_halt unitId vertex left).symm.trans
    ((congrArg (observe unitId vertex) same).trans (observe_halt unitId vertex right)))

variable {unitId : Nat} {imports : Tuple m.Val args} {locals : Locals m.Val past}
variable {store : σ} {vertex : Vertex Op args past outs}

private theorem vertex_exists (vertex : Vertex Op args past outs) :
    ∃ outcome, LinksVertex primitives unitId imports locals vertex store outcome := by
  cases vertex with
  | lambda => exact ⟨_, rfl⟩
  | phi => exact ⟨_, rfl⟩
  | delta delta =>
    obtain ⟨outcome, evaluated⟩ := eval_exists (primitives := primitives) delta.initializer.toTerm
      (delta.captures.read imports locals) PUnit.unit store
    cases outcome with
    | returned => exact ⟨_, LinksDelta.linked evaluated⟩
    | blocked => exact ⟨_, LinksDelta.undefined evaluated⟩

private theorem vertex_unique {left right : Outcome m σ outs}
    (first : LinksVertex primitives unitId imports locals vertex store left)
    (second : LinksVertex primitives unitId imports locals vertex store right) : left = right := by
  cases vertex with
  | lambda => exact first.trans second.symm
  | phi => exact first.trans second.symm
  | delta =>
    simp only [LinksVertex] at first second
    cases first with
    | linked first =>
      cases second with
      | linked second =>
        have equal := eval_observation_unique unitId past.length first second
        simp only [observation, Outcome.linked.injEq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        rfl
      | undefined second =>
        cases eval_observation_unique unitId past.length first second
    | undefined first =>
      cases second with
      | linked second => cases eval_observation_unique unitId past.length first second
      | undefined second =>
        have equal := eval_observation_unique unitId past.length first second
        simp only [observation, Outcome.undefined.injEq] at equal
        cases equal
        rfl

private theorem vertex_total (vertex : Vertex Op args past outs) :
    LinksVertex (Primitives.liftTotal m σ) unitId imports locals vertex store
      (.linked (Recursive.linkVertex m unitId imports locals vertex) store) := by
  cases vertex with
  | lambda => rfl
  | phi => rfl
  | delta delta =>
    exact LinksDelta.linked (Continuation.Partial.eval_liftTotal_iff.mpr
      ⟨embedded_returns delta.initializer.toTerm (delta.captures.read imports locals) PUnit.unit, rfl⟩)

private theorem table_exists (locals : Locals m.Val past) (table : VertexTable Op args past sigs)
    (results : Wires args (extend past sigs) outs) (store : σ) :
    ∃ outcome, LinksTable primitives unitId imports outs locals table results store outcome := by
  induction sigs generalizing past store with
  | nil => exact ⟨_, .ret locals table results store⟩
  | cons head tail ih =>
    obtain ⟨first, linked⟩ := vertex_exists (primitives := primitives) (unitId := unitId)
      (imports := imports) (locals := locals) (store := store) (table 0)
    cases first with
    | undefined => exact ⟨_, .stop linked⟩
    | linked values middle =>
      obtain ⟨outcome, more⟩ := ih (locals.snoc values) (fun i => table i.succ) results middle
      exact ⟨outcome, .bind linked more⟩

private theorem table_unique {table : VertexTable Op args past sigs}
    {results : Wires args (extend past sigs) outs} {left right : Outcome m σ outs}
    (first : LinksTable primitives unitId imports outs locals table results store left)
    (second : LinksTable primitives unitId imports outs locals table results store right) : left = right := by
  induction first with
  | ret => cases second; rfl
  | bind first more ih =>
    cases second with
    | bind second later =>
      obtain ⟨rfl, rfl⟩ := Outcome.linked.inj (vertex_unique first second)
      exact ih later
    | stop second => cases vertex_unique first second
  | stop first =>
    cases second with
    | bind second => cases vertex_unique first second
    | stop second => cases vertex_unique first second; rfl

private theorem table_total (locals : Locals m.Val past) (table : VertexTable Op args past sigs)
    (results : Wires args (extend past sigs) outs) (store : σ) :
    LinksTable (Primitives.liftTotal m σ) unitId imports outs locals table results store
      (.linked (Recursive.linkTable m unitId imports past sigs locals table results) store) := by
  induction sigs generalizing past with
  | nil => exact .ret locals table results store
  | cons head tail ih =>
    exact .bind (vertex_total (table 0))
      (ih (locals.snoc (Recursive.linkVertex m unitId imports locals (table 0))) (fun i => table i.succ) results)

private theorem vertex_undefined {failure : Failure m σ}
    (stopped : LinksVertex primitives unitId imports locals vertex store (.undefined failure)) :
    failure.unitId = unitId ∧ failure.vertex = past.length ∧ IsDelta vertex ∧
      (primitives.step failure.site.opcode failure.site.input).run failure.store = _root_.Part.none := by
  cases vertex with
  | lambda => cases stopped
  | phi => cases stopped
  | delta =>
    simp only [LinksVertex] at stopped
    cases stopped with
    | @undefined stopped site pending evaluation =>
      cases site
      obtain ⟨active, selected, action⟩ := evaluation.blocks (.halt : Continuation.Stack m _ _)
      change some _ = some active at selected
      cases Option.some.inj selected
      exact ⟨rfl, rfl, trivial, action⟩

private theorem table_undefined {table : VertexTable Op args past sigs}
    {results : Wires args (extend past sigs) outs} {outcome : Outcome m σ outs}
    (linked : LinksTable primitives unitId imports outs locals table results store outcome)
    {failure : Failure m σ} (failed : outcome = .undefined failure) :
    failure.unitId = unitId ∧
      (∃ i : Fin sigs.length, failure.vertex = past.length + i.val ∧ IsDelta (table i)) ∧
      (primitives.step failure.site.opcode failure.site.input).run failure.store = _root_.Part.none := by
  induction linked with
  | ret => cases failed
  | bind _ _ ih =>
    obtain ⟨unit, ⟨i, vertex, isDelta⟩, action⟩ := ih failed
    refine ⟨unit, ⟨i.succ, ?_, isDelta⟩, action⟩
    simp only [List.length_append, List.length_singleton, Fin.val_succ] at *
    omega
  | stop first =>
    cases failed
    obtain ⟨unit, vertex, isDelta, action⟩ := vertex_undefined first
    exact ⟨unit, ⟨0, by simpa only [Fin.val_zero, Nat.add_zero] using vertex, isDelta⟩, action⟩

theorem undefined_action {graph : Omega Op args outs sigs} {failure : Failure m σ}
    (stopped : Links primitives unitId graph imports store (.undefined failure)) :
    failure.unitId = unitId ∧
      (∃ i : Fin sigs.length, failure.vertex = i.val ∧ IsDelta (graph.region.vertices i)) ∧
      (primitives.step failure.site.opcode failure.site.input).run failure.store = _root_.Part.none := by
  obtain ⟨unit, ⟨i, vertex, isDelta⟩, action⟩ := table_undefined stopped rfl
  exact ⟨unit, ⟨i, by simpa only [List.length_nil, Nat.zero_add] using vertex, isDelta⟩, action⟩

theorem exists_outcome (graph : Omega Op args outs sigs) (store : σ) :
    ∃ outcome, Links primitives unitId graph imports store outcome :=
  table_exists (past := []) PUnit.unit graph.region.vertices graph.region.results store

theorem outcome_unique {graph : Omega Op args outs sigs} {left right : Outcome m σ outs}
    (first : Links primitives unitId graph imports store left)
    (second : Links primitives unitId graph imports store right) : left = right :=
  table_unique first second

theorem total_iff {graph : Omega Op args outs sigs} {outcome : Outcome m σ outs} :
    Links (Primitives.liftTotal m σ) unitId graph imports store outcome ↔
      outcome = .linked (Recursive.linkGraph m unitId graph imports) store := by
  have total : Links (Primitives.liftTotal m σ) unitId graph imports store
      (.linked (Recursive.linkGraph m unitId graph imports) store) :=
    table_total (past := []) PUnit.unit graph.region.vertices graph.region.results store
  exact ⟨(outcome_unique · total), (· ▸ total)⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Proofs
