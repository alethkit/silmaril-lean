module

public import Silmaril.SSA.PEG.Simple.While.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Translation

public section

namespace Silmaril.SSA.PEG.Simple.WhileProofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params all base nodes left right : List (Ty Data)} {out : Ty Data}

theorem portForall (ts : List (Ty Data)) (F : ∀ t, Port ts t → Prop)
    (h : ∀ i, F _ (portAt ts i)) (t : Ty Data) (p : Port ts t) : F t p := by
  induction ts with
  | nil => cases p
  | cons t ts ih =>
    cases p with
    | head => exact h 0
    | tail p => exact ih (fun t slot => F t (.tail slot)) (fun i => h i.succ) p

@[simp] theorem splitLeft (p : Port left out) :
    portSplit left (portLeft (right := right) p) = .inl p := by
  induction p with
  | head => rfl
  | tail p ih =>
    simp only [portLeft, portSplit, ih, Sum.map]
    rfl

@[simp] theorem splitRight (left : List (Ty Data)) (p : Port right out) :
    portSplit left (portRight left p) = .inr p := by
  induction left with
  | nil => rfl
  | cons t left ih =>
    simp only [portRight, portSplit, ih, Sum.map]
    rfl

theorem splitCases (left : List (Ty Data)) (r : Port (left ++ right) out) :
    (∃ p, r = portLeft p) ∨ (∃ p, r = portRight left p) := by
  induction left generalizing out with
  | nil => exact .inr ⟨r, rfl⟩
  | cons t rest ih =>
    cases r with
    | head => exact .inl ⟨.head, rfl⟩
    | tail r =>
      rcases ih r with ⟨p, rfl⟩ | ⟨p, rfl⟩
      · exact .inl ⟨.tail p, rfl⟩
      · exact .inr ⟨p, rfl⟩

theorem localRow (p : WhileProgram P params out) (neg : P [.bool] .bool)
    {t : Ty Data} (slot : Port p.core.nodes t) :
    p.row neg (p.localRef slot) = p.core.code.closeRows (p.thetaRow ·) (p.localRef ·) slot := by
  change p.tailRow (portLeft slot) = _
  simp only [WhileProgram.tailRow, splitLeft]

theorem paramRow (p : WhileProgram P params out) (neg : P [.bool] .bool)
    {t : Ty Data} (slot : Port params t) :
    p.row neg (p.paramRef slot) = ⟨_, .param slot, .nil⟩ := by
  change p.tailRow (portRight p.core.nodes slot) = _
  simp only [WhileProgram.tailRow, splitRight]

theorem liftedRow (code : Code P params base nodes)
    (holes : ∀ {t}, Port base t → WhileRow P params all t)
    (embed : ∀ {t}, Port nodes t → Port all t) (r : Port base out) :
    code.closeRows holes embed (code.lift r) = holes r := by
  induction code with
  | empty => rfl
  | emit prior label refs ih => exact ih (fun r => embed (.tail r))

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

@[expose] noncomputable def rowValue (r : WhileRow P params all out)
    (reads : ∀ {t}, Port all t → Index 1 → Option (m.Value t)) (i : Index 1) :
    Option (m.Value out) :=
  r.label.interpret m env i fun k j _ => reads (r.refs.get (portAt r.inputs k)) j

theorem equationAt (p : WhileProgram P params out) (neg : P [.bool] .bool)
    {values : (p.translate neg).Valuation m} (h : (p.translate neg).Solves m env values)
    (i : Index 1) (t : Ty Data) (r : Port p.layout t) :
    p.readPort neg m values r i = rowValue m env (p.row neg r) (p.readPort neg m values) i := by
  refine portForall p.layout (fun t r => p.readPort neg m values r i =
    rowValue m env (p.row neg r) (p.readPort neg m values) i) ?_ t r
  intro j
  have ref : numberPort (portAt p.layout j) = Ref.ofId (p.translate neg).sort j := by
    have idEq := Proofs.number_portAt p.layout j
    generalize numberPort (portAt p.layout j) = r at idEq ⊢
    cases r with
    | mk id ty =>
      change id = j at idEq
      subst id
      rfl
  unfold WhileProgram.readPort
  rw [ref]
  change values (j, i) = _
  rw [h (j, i)]
  unfold Graph.equation Graph.demandStep
  change ((p.row neg (portAt p.layout j)).label.interpret m env i _) = _
  unfold rowValue
  apply congrArg (((p.row neg (portAt p.layout j)).label).interpret m env i)
  funext k j' access
  have arg : ((p.translate neg).node j).arg k =
      numberPort ((p.row neg (portAt p.layout j)).refs.get (portAt _ k)) :=
    Proofs.get_map _ _ _
  exact congrArg (fun (ref : Ref (p.translate neg).sort ((p.translate neg).node j).inputs[k]) =>
    ref.read m.carrier (values (ref.id, j'))) arg

private theorem emitClosed (label : Label P params (Fin 0) left out)
    (refs : Tuple (Port nodes) left) (embed : ∀ {t}, Port nodes t → Port all t)
    (read : ∀ {t}, Port all t → Index 1 → Option (m.Value t))
    (i : Index 1) (vs : Proofs.NodeValues m nodes)
    (h : ∀ t (r : Port nodes t), read (embed r) i = vs.get r) :
    rowValue m env ⟨_, label.map (fun op => op) Fin.elim0, refs.map (fun _ slot => embed slot)⟩
      read i = emitValue m env label refs vs := by
  unfold rowValue emitValue
  cases label with
  | param => rfl
  | op instruction =>
    simp only [Label.map, Label.interpret, Proofs.get_map, h]
  | phi =>
    simp only [Label.map, Label.interpret, Proofs.get_map, h]
  | theta impossible | pass impossible | eval impossible => exact impossible.elim0

/-- The rows emitted over the holes solve the acyclic fragment pointwise. -/
theorem closedEval (code : Code P params base nodes)
    (holes : ∀ {t}, Port base t → WhileRow P params all t)
    (embed : ∀ {t}, Port nodes t → Port all t)
    (read : ∀ {t}, Port all t → Index 1 → Option (m.Value t)) (i : Index 1)
    (seed : Proofs.NodeValues m base)
    (seedOk : ∀ t (r : Port base t), read (embed (code.lift r)) i = seed.get r)
    (eqs : ∀ t (r : Port nodes t), read (embed r) i =
      rowValue m env (code.closeRows holes embed r) read i)
    (t : Ty Data) (r : Port nodes t) :
    read (embed r) i = (code.eval m env seed).get r := by
  induction code generalizing t with
  | empty => exact seedOk t r
  | emit prior label refs ih =>
    have earlier := ih (fun r => embed (.tail r)) seedOk (fun t r => eqs t (.tail r))
    cases r with
    | head =>
      rw [eqs]
      exact emitClosed m env label refs (fun r => embed (.tail r)) read i _ earlier
    | tail r => exact earlier _ r

end Silmaril.SSA.PEG.Simple.WhileProofs
