module

public import Silmaril.SSA.PEG.Simple.Graph
public import Silmaril.SSA.PEG.Semantics.Thms
public import Silmaril.SSA.PEG.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w x y

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before mid after ins roots : List (Ty Data)} {out : Ty Data}

theorem get_map {F : Ty Data → Type w} {G : Ty Data → Type x}
    (values : Tuple F before) (f : ∀ t, F t → G t) (p : Port before out) :
    (values.map f).get p = f out (values.get p) := by
  induction p with
  | head => cases values; rfl
  | tail p ih => cases values with | cons _ tail => exact ih tail

theorem map_map {F : Ty Data → Type w} {G : Ty Data → Type x} {H : Ty Data → Type y}
    (values : Tuple F before) (f : ∀ t, F t → G t) (h : ∀ t, G t → H t) :
    (values.map f).map h = values.map (fun t x => h t (f t x)) := by
  induction values with
  | nil => rfl
  | cons _ _ ih => simp only [Tuple.map, ih]

theorem get_select {F : Ty Data → Type w} (values : Tuple F before)
    (refs : Tuple (Port before) ins) (slot : Port ins out) :
    (select values refs).get slot = values.get (refs.get slot) :=
  get_map refs (fun _ r => values.get r) slot

variable (m : Interpretation.{u,v,w} P)
variable (input : Tuple m.Value params)
variable (base : Tuple (fun t => Option (m.Value t)) before)

theorem eval_lift (code : Code P params before after) (p : Port before out) :
    (code.eval m input base).get (code.lift p) = base.get p := by
  induction code with
  | empty => rfl
  | emit _ _ _ ih => exact ih

theorem eval_append (prefixCode : Code P params before mid) (suffixCode : Code P params mid after) :
    (prefixCode.append suffixCode).eval m input base =
      suffixCode.eval m input (prefixCode.eval m input base) := by
  induction suffixCode with
  | empty => rfl
  | emit _ _ _ ih => simp only [Code.append, Code.eval, ih]

theorem select_lift (code : Code P params before after) (refs : Tuple (Port before) ins) :
    select (code.eval m input base) (code.liftRefs refs) = select base refs := by
  unfold select Code.liftRefs
  simp only [map_map, eval_lift]

private theorem emitValue_weaken (label : Label P params (Fin 0) ins out)
    (refs : Tuple (Port before) ins) {t : Ty Data} (value : Option (m.Value t)) :
    emitValue m input label (refs.map fun _ p => Port.tail p) (.cons value base) =
      emitValue m input label refs base := by
  unfold emitValue
  apply congrArg (label.interpret m input Index.zero)
  funext slot j access
  rw [get_map]
  rfl

private theorem eval_row (code : Code P params [] after) (p : Port after out) :
    (code.eval m input .nil).get p =
      emitValue m input (code.row p).label (code.row p).refs (code.eval m input .nil) := by
  induction code with
  | empty => cases p
  | emit prior label refs ih =>
    cases p with
    | head => exact (emitValue_weaken m input (prior.eval m input .nil) label refs _).symm
    | tail p =>
      exact (ih p).trans
        (emitValue_weaken m input (prior.eval m input .nil) (prior.row p).label (prior.row p).refs _).symm

private theorem number_portAt : (ts : List (Ty Data)) → (i : Fin ts.length) →
    (numberPort (portAt ts i)).id = i
  | [], i => i.elim0
  | _ :: ts, i => Fin.cases rfl (fun j => congrArg Fin.succ (number_portAt ts j)) i

private theorem numberPort_read (values : Tuple (fun t => Option (m.Value t)) after)
    (p : Port after out) :
    (numberPort p).read m.carrier (values.get (portAt after (numberPort p).id)) = values.get p := by
  induction p with
  | head => cases values; rfl
  | tail p ih => cases values with | cons _ tail => exact ih tail

private theorem row_bound (code : Code P params [] after) (p : Port after out)
    {arg : Ty Data} (slot : Port (code.row p).inputs arg) :
    (numberPort p).id.val < (numberPort ((code.row p).refs.get slot)).id.val := by
  induction code with
  | empty => cases p
  | emit prior label refs ih =>
    cases p with
    | head =>
      change 0 < (numberPort ((refs.map fun _ q => Port.tail q).get slot)).id.val
      rw [get_map]
      exact Nat.zero_lt_succ _
    | tail p =>
      change (numberPort p).id.val + 1 <
        (numberPort (((prior.row p).refs.map fun _ q => Port.tail q).get slot)).id.val
      rw [get_map]
      exact Nat.succ_lt_succ (ih p slot)

theorem edge_forward (code : Code P params [] after) (outputs : Tuple (Port after) roots)
    {a b : Fin after.length} {kind : EdgeKind (Fin 0)}
    (edge : (code.toGraph outputs).Edge a kind b) : a.val < b.val := by
  obtain ⟨slot, _, eq⟩ := edge
  let p := portAt after a
  let row := code.row p
  change ((row.refs.map fun _ p => numberPort p).get (portAt row.inputs slot)).id = b at eq
  rw [get_map] at eq
  have lt := row_bound code p (portAt row.inputs slot)
  change (numberPort (portAt after a)).id.val <
    (numberPort (row.refs.get (portAt row.inputs slot))).id.val at lt
  rw [number_portAt, eq] at lt
  exact lt

theorem toGraph_wellFormed (code : Code P params [] after) (outputs : Tuple (Port after) roots) :
    (code.toGraph outputs).WellFormed where
  forest := fun i => i.elim0
  feedback := by
    intro a ks walk positive
    have decrease := walk.strictRank positive (fun i => after.length - i.val) fun edge _ => by
      have := edge_forward code outputs edge
      omega
    exact (Nat.lt_irrefl _ decrease).elim
  loopScope := fun _ _ _ loop => loop.elim0
  outerFeedback := fun _ _ _ _ _ loop => loop.elim0

private theorem values_solve (code : Code P params [] after) (outputs : Tuple (Port after) roots) :
    (code.toGraph outputs).Solves m input
      (fun q => (code.eval m input .nil).get (portAt after q.1)) := by
  rintro ⟨i, idx⟩
  have same : idx = Index.zero := funext fun x => x.elim0
  subst idx
  refine (eval_row m input code (portAt after i)).trans ?_
  unfold emitValue Graph.equation Graph.demandStep
  let row := code.row (portAt after i)
  apply congrArg (row.label.interpret m input Index.zero)
  funext slot j access
  let p := row.refs.get (portAt row.inputs slot)
  have arg : ((code.toGraph outputs).node i).arg slot = numberPort p :=
    get_map row.refs (fun _ p => numberPort p) (portAt row.inputs slot)
  change (code.eval m input .nil).get p =
    (((code.toGraph outputs).node i).arg slot).read m.carrier
      ((code.eval m input .nil).get
        (portAt after (((code.toGraph outputs).node i).arg slot).id))
  rw [arg]
  exact (numberPort_read m _ p).symm

private theorem select_numbered (values : Tuple (fun t => Option (m.Value t)) after)
    (outputs : Tuple (Port after) roots) :
    (outputs.map (fun _ p => numberPort p)).map
        (fun _ r => r.read m.carrier (values.get (portAt after r.id))) =
      select values outputs := by
  simp only [select, map_map, numberPort_read]

theorem observe_toGraph (code : Code P params [] after) (outputs : Tuple (Port after) roots)
    (wf : WellFounded (code.toGraph outputs).Demand) (idx : Index 0) :
    (code.toGraph outputs).observe m ((code.toGraph outputs).denote m input wf) idx =
      select (code.eval m input .nil) outputs := by
  have denote := (code.toGraph outputs).denote_solves m input wf
  have eq := (code.toGraph outputs).solves_unique m input wf denote
    (values_solve m input code outputs)
  rw [eq]
  exact select_numbered m _ outputs

end Silmaril.SSA.PEG.Simple.Proofs
