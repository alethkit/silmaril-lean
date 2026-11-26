module

public import Silmaril.SSA.PEG.Simple.Revert.Defs
public import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Proofs

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params ins : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P params [result] n 0} {m : Interpretation.{u,v,w} P}
variable {input : Tuple m.Value params} {values : g.Valuation m} {idx : Index 0}
variable {live needed : List (Fin n)}

private theorem ordinary {out : Ty Data} (label : Label P params (Fin 0) ins out)
    (slot : Fin ins.length) : label.kind slot = .ordinary := by
  cases label with
  | param _ | op _ | phi => rfl
  | theta l | eval l | pass l => exact l.elim0

theorem depthZero (wf : WellFounded g.Demand) (i : Fin n) : DepthZero g i := by
  let motive := fun q : Request n 0 => DepthZero g q.1
  apply wf.induction (C := motive) (i, Index.zero)
  intro q ih
  exact .node fun slot => ih (((g.node q.1).arg slot).id, q.2)
    ⟨.ordinary, ⟨slot, ordinary (g.node q.1).label slot, rfl⟩, rfl⟩

private def atRef (values : g.Valuation m) (idx : Index 0) (r : Ref g.sort t) :
    Option (m.Value t) := r.read m.carrier (values (r.id, idx))

private theorem definedAt {r : Ref g.sort t} {v : m.Value t}
    (h : atRef values idx r = some v) : ∃ x, values (r.id, idx) = some x := by
  rcases r with ⟨i, hsort⟩
  subst t
  exact ⟨v, h⟩

private theorem rowValue (solves : g.Solves m input values) {i : Fin n}
    {label : Label P params (Fin 0) ins (g.sort i)} {refs : Tuple (Ref g.sort) ins}
    (row : g.node i = Node.ofLabel label refs) :
    values (i, idx) = label.interpret m input idx
      (fun slot j _ => atRef values j (refs.get (portAt ins slot))) := by
  rw [solves (i, idx)]
  change (let node := g.node i
          node.label.interpret m input idx (fun slot j _ => atRef values j (node.arg slot))) = _
  rw [row]
  rfl

private theorem collectRead {ts : List (Ty Data)}
    {read : ∀ s : Fin ts.length, Option (m.Value ts[s])} {xs : Tuple m.Value ts}
    (h : collect ts read = some xs) (slot : Fin ts.length) :
    ∃ x, read slot = some x := by
  induction ts with
  | nil => exact slot.elim0
  | cons t ts ih =>
    cases ha : read 0 with
    | none => simp [collect, ha] at h
    | some x =>
      cases hb : collect ts (fun s => read s.succ) with
      | none => simp [collect, ha, hb] at h
      | some ys => exact Fin.cases ⟨x, ha⟩ (fun j => ih hb j) slot

private def Demanded (values : g.Valuation m) (idx : Index 0) (needed : List (Fin n)) : Prop :=
  ∀ ⦃i⦄, i ∈ needed → ∃ value, values (i, idx) = some value

private theorem demandSelected {r : Ref g.sort t} {value : m.Value t}
    (selected : atRef values idx r = some value) (entry : Demanded values idx needed) :
    Demanded values idx (r.id :: needed) := by
  intro i hi
  rcases List.mem_cons.mp hi with rfl | hi
  · exact definedAt selected
  · exact entry hi

private theorem strictRead {out : Ty Data} (label : Label P params (Fin 0) ins out)
    (refs : Tuple (Ref g.sort) ins)
    {value : m.Value out}
    (h : label.interpret m input idx
      (fun slot j _ => atRef values j (refs.get (portAt ins slot))) = some value)
    (slot : Fin ins.length) (needed : slot ∈ strictSlots label) :
    ∃ x, atRef values idx (refs.get (portAt ins slot)) = some x := by
  cases label with
  | param _ => simp [strictSlots] at needed
  | op instr =>
    cases hc : collect _ (fun s => atRef values idx (refs.get (portAt _ s))) with
    | none => simp [Label.interpret, hc] at h
    | some xs => exact collectRead hc slot
  | phi =>
    simp only [strictSlots, List.mem_singleton] at needed
    subst slot
    change ((atRef values idx (refs.get (portAt [.bool, out, out] 0))).elim none
      (fun flag => if flag.down then atRef values idx (refs.get (portAt [.bool, out, out] 1))
        else atRef values idx (refs.get (portAt [.bool, out, out] 2)))) = some value at h
    cases hc : atRef values idx (refs.get (portAt [.bool, out, out] 0)) with
    | none => rw [hc] at h; cases h
    | some flag => exact ⟨flag, rfl⟩
  | theta l | eval l | pass l => exact l.elim0

private theorem reveal (solves : g.Solves m input values) {i : Fin n}
    (hi : i ∈ needed) (entry : Demanded values idx needed) :
    Demanded values idx (strictInputs g i ++ needed) := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · obtain ⟨value, hv⟩ := entry hi
    rcases List.mem_map.mp hj with ⟨slot, hs, rfl⟩
    have eq := rowValue (idx := idx) solves
      (refs := (g.node i).args) (label := (g.node i).label) (i := i) rfl
    obtain ⟨x, hx⟩ := strictRead _ _ (eq.symm.trans hv) slot hs
    exact definedAt hx
  · exact entry hj

private structure Realizes (values : g.Valuation m) (idx : Index 0)
    (input : Tuple m.Value params) (store : Tuple m.Value (vars g.sort params live)) : Prop where
  nodes : ∀ {i} (slot : Port live i), values (i, idx) = some (store.get (localPort slot))
  params : ∀ {t} (slot : Port params t), store.get (paramPort live slot) = input.get slot

private theorem Realizes.cons {store : Tuple m.Value (vars g.sort params live)} {i : Fin n}
    {x : m.Value (g.sort i)} (entry : Realizes values idx input store)
    (hx : values (i, idx) = some x) :
    Realizes (live := i :: live) values idx input (.cons x store) where
  nodes slot := by
    cases slot with
    | head => exact hx
    | tail p => exact entry.nodes p
  params p := entry.params p

private theorem Realizes.read {store : Tuple m.Value (vars g.sort params live)} {r : Ref g.sort t}
    (entry : Realizes values idx input store) (p : Port live r.id) :
    atRef values idx r = some (store.get (refPort r p)) := by
  rcases r with ⟨i, h⟩
  subst t
  exact entry.nodes p

private theorem evalReads {store : Tuple m.Value (vars g.sort params live)}
    (entry : Realizes values idx input store) {refs : Tuple (Ref g.sort) ins}
    (reads : Reads g.sort live refs) :
    collect ins (fun s => atRef values idx (refs.get (portAt ins s))) =
      (reads.args (P := P)).eval m store := by
  induction reads with
  | nil => rfl
  | @cons t ts r rs head tail ih =>
    simp only [collect, Reads.args, Args.eval, Expr.evalLift]
    have readHead :
        atRef values idx ((Tuple.cons r rs).get (portAt (t :: ts) 0)) = atRef values idx r := rfl
    have readTail :
        (fun (s : Fin ts.length) => atRef values idx ((Tuple.cons r rs).get (portAt (t :: ts) s.succ))) =
          (fun s => atRef values idx (rs.get (portAt ts s))) := rfl
    rw [readHead, readTail, entry.read head, ih]
    cases (tail.args (P := P)).eval m store <;> rfl

private theorem tupleExt {ts : List (Ty Data)} {a b : Tuple m.Value ts}
    (h : ∀ {t} (p : Port ts t), a.get p = b.get p) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys =>
      have hhead : x = y := h .head
      have htail : xs = ys := ih (fun p => h (.tail p))
      rw [hhead, htail]

private theorem selectEntry {vs : List (Ty Data)} {tmp out : Ty Data}
    (store : Tuple m.Value vs) (temp : m.Value tmp) (value : m.Value out) :
    select (.cons value (.cons temp store))
      (.cons .head ((ports vs).map fun _ p => .tail (.tail p))) = .cons value store := by
  apply tupleExt
  intro t p
  rw [select, get_map]
  cases p with
  | head => rfl
  | tail p =>
    change (Tuple.cons value (.cons temp store)).get
      (((ports vs).map fun _ p => Port.tail (Port.tail p)).get p) = store.get p
    rw [get_map, ports_get]
    rfl

private theorem keepEntryRun {vs : List (Ty Data)} {tmp out : Ty Data}
    {step : Stmt P false vs (tmp :: vs)} {next : Stmt P false (tmp :: vs) (out :: tmp :: vs)}
    {store : Tuple m.Value vs} {temp : m.Value tmp} {value : m.Value out}
    (first : Exec m step store (some (.cons temp store)))
    (rest : Exec m next (.cons temp store) (some (.cons value (.cons temp store)))) :
    Exec m (keepEntry step next) store (some (.cons value store)) := by
  refine .seq first (.seq rest ?_)
  exact selectEntry store temp value ▸ Exec.project

private theorem scheduleRun (solves : g.Solves m input values) {root : Ref g.sort t}
    (plan : Schedule g root live needed)
    {store : Tuple m.Value (vars g.sort params live)} {value : m.Value t}
    (entry : Realizes values idx input store) (demand : Demanded values idx needed)
    (rootValue : atRef values idx root = some value) :
    Exec m plan.lower store (some (.cons value store)) := by
  induction plan with
  | done slot =>
    have eq := (entry.read slot).symm.trans rootValue
    change some _ = some _ at eq
    have out := Option.some.inj eq
    have proj : select store (.cons (refPort _ slot) (ports _)) = .cons value store := by
      apply tupleExt
      intro t p
      rw [select, get_map]
      cases p with
      | head => exact out
      | tail p => exact congrArg store.get (ports_get p)
    exact proj ▸ Exec.project
  | reveal _ demanded _ ih => exact ih entry (reveal solves demanded demand) rootValue
  | param i _ slot row _ ih =>
    have hx : values (i, idx) = some (store.get (paramPort _ slot)) := by
      simpa only [Label.interpret, entry.params slot] using (rowValue (idx := idx) solves row)
    exact keepEntryRun (.assign rfl) (ih (entry.cons hx) demand rootValue)
  | op i demanded instr _ row reads _ ih =>
    obtain ⟨x, hx⟩ := demand demanded
    have eq := rowValue (idx := idx) solves row
    rw [hx] at eq
    simp only [Label.interpret, evalReads entry reads] at eq
    exact keepEntryRun (.assign eq.symm) (ih (entry.cons hx) demand rootValue)
  | branch i demanded guard yes no row slot yesArm noArm _ ihYes ihNo ihNext =>
    obtain ⟨x, hx⟩ := demand demanded
    have eq := rowValue (idx := idx) solves row
    rw [hx] at eq
    have phiValue : some x = (atRef values idx guard).elim none
        (fun flag => if flag.down then atRef values idx yes else atRef values idx no) := eq
    rw [entry.read slot] at phiValue
    have runBranch : Exec m (.branch (.var (refPort guard slot)) yesArm.lower noArm.lower) store
        (some (.cons x store)) := by
      cases hflag : store.get (refPort guard slot) with
      | up flag =>
        cases flag
        · have selected : atRef values idx no = some x := by
            rw [hflag] at phiValue
            exact phiValue.symm
          exact .branchFalse (congrArg some hflag)
            (ihNo entry (demandSelected selected demand) selected)
        · have selected : atRef values idx yes = some x := by
            rw [hflag] at phiValue
            exact phiValue.symm
          exact .branchTrue (congrArg some hflag)
            (ihYes entry (demandSelected selected demand) selected)
    exact keepEntryRun runBranch (ihNext (entry.cons hx) demand rootValue)

theorem returns (cert : Certificate g) (wf : WellFounded g.Demand) (input : Tuple m.Value params)
    (idx : Index 0) (value : m.Value result)
    (defined : g.observe m (g.denote m input wf) idx = .cons (some value) .nil) :
    cert.revert.Returns m input value := by
  let values := g.denote m input wf
  have solved := g.denote_solves m input wf
  have rootValue : atRef values idx (returnRef g) = some value := by
    have h := congrArg (fun xs : Tuple (fun t => Option (m.Value t)) [result] => xs.get .head) defined
    rw [Graph.observe, get_map] at h
    exact h
  have entry : Realizes (live := []) values idx input input := by
    constructor
    · intro _ p
      exact nomatch p
    · intro _ _
      rfl
  have demanded : Demanded values idx [(returnRef g).id] := by
    intro i hi
    have hi := List.mem_singleton.mp hi
    subst i
    exact definedAt rootValue
  exact ⟨.cons value input, scheduleRun solved cert.schedule entry demanded rootValue, rfl⟩

end Silmaril.SSA.PEG.Simple.Revert.Proofs
