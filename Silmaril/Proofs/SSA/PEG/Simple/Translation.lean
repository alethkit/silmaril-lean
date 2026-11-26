module

public import Silmaril.Proofs.SSA.PEG.Simple.Graph
public import Silmaril.SSA.PEG.Simple.Translate

public section

namespace Silmaril.SSA.PEG.Simple.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable (m : Interpretation.{u,v,w} P)
variable {params vars outs nodes newNodes : List (Ty Data)}

abbrev NodeValues (nodes : List (Ty Data)) := Tuple (fun t => Option (m.Value t)) nodes

variable (input : Tuple m.Value params)

private theorem realizes_lift (code : Code P params nodes newNodes)
    {values : NodeValues m nodes} {ctx : Tuple (Port nodes) vars} {store : Tuple m.Value vars}
    (h : Realizes m values ctx store) :
    Realizes m (code.eval m input values) (code.liftRefs ctx) store := by
  intro t p
  unfold Code.liftRefs
  rw [get_map, eval_lift]
  exact h _ p

private theorem collect_defined (store : Tuple m.Value vars) :
    collect vars (fun slot => some (store.get (portAt vars slot))) = some store := by
  induction store with
  | nil => rfl
  | cons value tail ih => simp [collect, portAt, Tuple.get, ih]

private theorem collect_realizes {values : NodeValues m nodes}
    {ctx : Tuple (Port nodes) vars} {store : Tuple m.Value vars}
    (h : Realizes m values ctx store) :
    collect vars (fun slot => values.get (ctx.get (portAt vars slot))) = some store := by
  have reads : (fun slot : Fin vars.length => values.get (ctx.get (portAt vars slot))) =
      fun slot => some (store.get (portAt vars slot)) :=
    funext fun slot => h _ (portAt vars slot)
  exact reads ▸ collect_defined m store

mutual

theorem expr_correct {out : Ty Data} (e : Expr P vars out)
    {nodes : List (Ty Data)} (ctx : Tuple (Port nodes) vars) (values : NodeValues m nodes)
    (store : Tuple m.Value vars) (h : Realizes m values ctx store)
    {value : m.Value out} (source : e.eval m store = some value) :
    let b := e.lower (params := params) ctx
    (b.code.eval m input values).get (b.refs.get .head) = some value := by
  dsimp only
  cases e with
  | var p =>
    change some (store.get p) = some value at source
    exact (h _ p).trans source
  | op instr args =>
    cases success : args.eval m store with
    | none => simp [Expr.eval, Expr.evalLift, success] at source
    | some tuple =>
      have matched := args_correct args ctx values store h success
      change emitValue m input (.op instr) (args.lower (params := params) ctx).refs
        ((args.lower (params := params) ctx).code.eval m input values) = some value
      change (collect _ (fun slot => ((args.lower (params := params) ctx).code.eval m input values).get
        ((args.lower (params := params) ctx).refs.get (portAt _ slot)))).elim none
        (m.run instr) = some value
      rw [collect_realizes m matched]
      simpa only [Expr.eval, Expr.evalLift, success, Option.elim_some] using source

theorem args_correct {outs : List (Ty Data)} (a : Args P vars outs)
    {nodes : List (Ty Data)} (ctx : Tuple (Port nodes) vars) (values : NodeValues m nodes)
    (store : Tuple m.Value vars) (h : Realizes m values ctx store)
    {tuple : Tuple m.Value outs} (source : a.eval m store = some tuple) :
    let b := a.lower (params := params) ctx
    Realizes m (b.code.eval m input values) b.refs tuple := by
  dsimp only
  cases a with
  | nil => intro t p; cases p
  | cons e es =>
    change (match e.eval m store, es.eval m store with
      | some val, some vs => some (Tuple.cons val vs)
      | _, _ => none) = some tuple at source
    cases headEq : e.eval m store with
    | none => simp [headEq] at source
    | some value =>
      cases tailEq : es.eval m store with
      | none => simp [headEq, tailEq] at source
      | some tail =>
        have eq : Tuple.cons value tail = tuple := by
          simpa [headEq, tailEq] using source
        subst tuple
        let head := e.lower (params := params) ctx
        let rest := es.lower (params := params) (head.code.liftRefs ctx)
        have hHead := expr_correct e ctx values store h headEq
        have hRest := args_correct es (head.code.liftRefs ctx) (head.code.eval m input values)
          store (realizes_lift m input head.code h) tailEq
        intro t p
        cases p with
        | head =>
          change ((head.code.append rest.code).eval m input values).get
            (rest.code.lift (head.refs.get .head)) = some value
          rw [eval_append, eval_lift]
          exact hHead
        | tail p =>
          change ((head.code.append rest.code).eval m input values).get (rest.refs.get p) =
            some (tail.get p)
          rw [eval_append]
          exact hRest _ p

end

private theorem phi_correct (condition : Port nodes .bool)
    (yes no : Tuple (Port nodes) outs) (values : NodeValues m nodes) (b : Bool)
    (test : values.get condition = some ⟨b⟩) (out : Tuple m.Value outs)
    (arm : Realizes m values (if b then yes else no) out) :
    let result := phiNodes (P := P) (params := params) condition yes no
    Realizes m (result.code.eval m input values) result.refs out := by
  dsimp only
  induction out with
  | nil => intro t p; cases p
  | cons value rest ih =>
    cases yes with
    | cons y ys =>
      cases no with
      | cons n ns =>
        let tail := phiNodes (P := P) (params := params) condition ys ns
        have tailArm : Realizes m values (if b then ys else ns) rest := by
          intro t slot
          cases b
          · exact arm _ (.tail slot)
          · exact arm _ (.tail slot)
        have tailOk := ih ys ns tailArm
        intro t slot
        cases slot with
        | head =>
          let vs := tail.code.eval m input values
          change (vs.get (tail.code.lift condition)).elim none (fun flag =>
            if flag.down then vs.get (tail.code.lift y) else vs.get (tail.code.lift n)) = some value
          dsimp only [vs]
          rw [eval_lift, test]
          cases b
          · change (tail.code.eval m input values).get (tail.code.lift n) = some value
            rw [eval_lift]
            exact arm _ .head
          · change (tail.code.eval m input values).get (tail.code.lift y) = some value
            rw [eval_lift]
            exact arm _ .head
        | tail slot =>
          change (Tuple.cons _ (tail.code.eval m input values)).get
            ((tail.refs.map fun _ p => Port.tail p).get slot) = some (rest.get slot)
          rw [get_map]
          exact tailOk _ slot

private theorem branch_correct (guard : Expr P vars .bool) (yes no : Stmt P false vars outs)
    (ctx : Tuple (Port nodes) vars) (values : NodeValues m nodes) (store : Tuple m.Value vars)
    (h : Realizes m values ctx store) (b : Bool) (test : guard.eval m store = some ⟨b⟩)
    (out : Tuple m.Value outs)
    (chosen : ∀ {nodes : List (Ty Data)} (ctx : Tuple (Port nodes) vars) (base : NodeValues m nodes),
      Realizes m base ctx store →
      let lowered := (if b then yes else no).lower (params := params) ctx
      Realizes m (lowered.code.eval m input base) lowered.refs out) :
    let lowered := (Stmt.branch guard yes no).lower (params := params) ctx
    Realizes m (lowered.code.eval m input values) lowered.refs out := by
  simp only [Stmt.lower, Build.thenBuild]
  let c := guard.lower (params := params) ctx
  let entry := c.code.liftRefs ctx
  let y := yes.lower (params := params) entry
  let n := no.lower (params := params) (y.code.liftRefs entry)
  let cVals := c.code.eval m input values
  let yVals := y.code.eval m input cVals
  let nVals := n.code.eval m input yVals
  let condition := n.code.lift (y.code.lift (c.refs.get .head))
  let chosenRefs := phiNodes (P := P) (params := params) condition (n.code.liftRefs y.refs) n.refs
  have atEntry : Realizes m cVals entry store := realizes_lift m input c.code h
  have conditionOk : nVals.get condition = some ⟨b⟩ := by
    dsimp [nVals, yVals, condition, cVals]
    rw [eval_lift, eval_lift]
    exact expr_correct m input guard ctx values store h test
  have selected : Realizes m nVals (if b then n.code.liftRefs y.refs else n.refs) out := by
    cases b
    · exact chosen (y.code.liftRefs entry) yVals (realizes_lift m input y.code atEntry)
    · exact realizes_lift m input n.code (chosen entry cVals atEntry)
  change Realizes m ((c.code.append (y.code.append (n.code.append chosenRefs.code))).eval m input values)
    chosenRefs.refs out
  rw [eval_append, eval_append, eval_append]
  exact phi_correct m input condition (n.code.liftRefs y.refs) n.refs nVals b conditionOk out selected

theorem stmt_correct {vars outs : List (Ty Data)} (s : Stmt P false vars outs)
    {nodes : List (Ty Data)} (ctx : Tuple (Port nodes) vars)
    (values : NodeValues m nodes) {store : Tuple m.Value vars} {out : Tuple m.Value outs}
    (h : Realizes m values ctx store) (source : Exec m s store (some out)) :
    let b := s.lower (params := params) ctx
    Realizes m (b.code.eval m input values) b.refs out := by
  dsimp only
  induction s generalizing nodes with
  | assign rhs =>
    cases source with
    | assign eval =>
      intro t slot
      cases slot with
      | head => exact expr_correct m input rhs ctx values store h eval
      | tail slot => exact realizes_lift m input (rhs.lower (params := params) ctx).code h _ slot
  | project slots =>
    cases source
    intro t p
    change values.get ((select ctx slots).get p) = some ((select store slots).get p)
    rw [get_select, get_select]
    exact h _ (slots.get p)
  | seq first second ihFirst ihSecond =>
    cases source with
    | seq runFirst runSecond =>
      let a := first.lower (params := params) ctx
      let b := second.lower (params := params) a.refs
      change Realizes m ((a.code.append b.code).eval m input values) b.refs out
      rw [eval_append]
      exact ihSecond a.refs _ (ihFirst ctx values h runFirst) runSecond
  | branch guard yes no ihYes ihNo =>
    cases source with
    | branchTrue test arm =>
      exact branch_correct m input guard yes no ctx values store h true test out
        (fun chosenCtx chosenBase matchEntry => ihYes chosenCtx chosenBase matchEntry arm)
    | branchFalse test arm =>
      exact branch_correct m input guard yes no ctx values store h false test out
        (fun chosenCtx chosenBase matchEntry => ihNo chosenCtx chosenBase matchEntry arm)
  | «while» impossible _ _ _ => nomatch impossible

private theorem param_correct (slots : Tuple (Port params) outs) (base : NodeValues m nodes) :
    let b := paramNodes (P := P) (nodes := nodes) slots
    Realizes m (b.code.eval m input base) b.refs (select input slots) := by
  dsimp only
  induction slots with
  | nil => intro t p; cases p
  | cons port ports ih =>
    let b := paramNodes (P := P) (nodes := nodes) ports
    intro t slot
    cases slot with
    | head => rfl
    | tail slot =>
      change (Tuple.cons _ (b.code.eval m input base)).get
        ((b.refs.map fun _ p => Port.tail p).get slot) = some ((select input ports).get slot)
      rw [get_map]
      exact ih _ slot

private theorem ports_get {out : Ty Data} (p : Port params out) : (ports params).get p = p := by
  induction p with
  | head => rfl
  | tail p ih =>
    change ((ports _).map fun _ r => Port.tail r).get p = Port.tail p
    rw [get_map, ih]

theorem program_correct {out : Ty Data} (p : Program P false params out) {value : m.Value out}
    (source : p.Returns m input value) (wf : WellFounded p.translate.Demand) (idx : Index 0) :
    p.translate.observe m (p.translate.denote m input wf) idx = .cons (some value) .nil := by
  obtain ⟨final, run, returns⟩ := source
  let entry := paramNodes (P := P) (nodes := []) (ports params)
  let body := p.body.lower (params := params) entry.refs
  have paramsOk : Realizes m (entry.code.eval m input .nil) entry.refs input := by
    intro t slot
    have eq := param_correct m input (ports params) .nil _ slot
    rw [get_select, ports_get] at eq
    exact eq
  have outOk := stmt_correct m input p.body entry.refs (entry.code.eval m input .nil) paramsOk run
  change (p.lower.code.toGraph p.lower.refs).observe m
    ((p.lower.code.toGraph p.lower.refs).denote m input wf) idx = _
  rw [observe_toGraph]
  change Tuple.cons (F := fun t => Option (m.Value t))
    (((entry.code.append body.code).eval m input .nil).get (body.refs.get p.retvar)) .nil =
      .cons (some value) .nil
  rw [eval_append, outOk _ p.retvar, returns]

end Silmaril.SSA.PEG.Simple.Proofs
