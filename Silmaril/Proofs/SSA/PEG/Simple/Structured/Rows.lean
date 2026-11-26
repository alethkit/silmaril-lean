module

public import Silmaril.SSA.PEG.Simple.Structured.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.While.Rows

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars inside all : List (Ty Data)} {t : Ty Data}

theorem straightRows_lift (code : Simple.Code P params before after)
    (holes : Rows P params before all) (embed : Embed after all) (r : Port before t) :
    straightRows holes code embed (code.lift r) = holes r := by
  induction code with
  | empty => rfl
  | emit prior label refs ih => exact ih (fun r => embed (.tail r))

theorem loopHoles_left (body : Code P params (vars ++ before) inside)
    (init : Tuple (Port before) vars) (next : Tuple (Port inside) vars)
    (holes : Rows P params before all) (embed : Embed (vars ++ .count :: .bool :: inside) all)
    (slot : Port vars t) :
    loopHoles body init next holes embed (portLeft slot) =
      ⟨_, .theta (numberPort (embed (passRef vars))).id,
        .cons (embed (insideRef vars (body.lift (portRight vars (init.get slot)))))
          (.cons (embed (insideRef vars (next.get slot))) .nil), none⟩ := by
  simp only [loopHoles, WhileProofs.splitLeft]

theorem loopHoles_right (body : Code P params (vars ++ before) inside)
    (init : Tuple (Port before) vars) (next : Tuple (Port inside) vars)
    (holes : Rows P params before all) (embed : Embed (vars ++ .count :: .bool :: inside) all)
    (r : Port before t) :
    loopHoles body init next holes embed (portRight vars r) = holes r := by
  simp only [loopHoles, WhileProofs.splitRight]

theorem loopRows_exit (body : Code P params (vars ++ before) inside)
    (guard : Port inside .bool) (neg : P [.bool] .bool) (parent : Option (Fin all.length))
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (inner : Rows P params inside all)
    (slot : Port vars t) :
    loopRows body guard neg parent embed inner (portLeft slot) =
      ⟨_, .eval (numberPort (embed (passRef vars))).id,
        .cons (embed (insideRef vars (body.lift (portLeft slot))))
          (.cons (embed (passRef vars)) .nil), none⟩ := by
  simp only [loopRows, WhileProofs.splitLeft]

theorem loopRows_pass (body : Code P params (vars ++ before) inside)
    (guard : Port inside .bool) (neg : P [.bool] .bool) (parent : Option (Fin all.length))
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (inner : Rows P params inside all) :
    loopRows body guard neg parent embed inner (passRef vars) =
      ⟨_, .pass (numberPort (embed (passRef vars))).id, .cons (embed (negRef vars)) .nil, parent⟩ := by
  simp only [passRef, loopRows, WhileProofs.splitRight, portConsCases]

theorem loopRows_neg (body : Code P params (vars ++ before) inside)
    (guard : Port inside .bool) (neg : P [.bool] .bool) (parent : Option (Fin all.length))
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (inner : Rows P params inside all) :
    loopRows body guard neg parent embed inner (negRef vars) =
      ⟨_, .op neg, .cons (embed (insideRef vars guard)) .nil, none⟩ := by
  simp only [negRef, loopRows, WhileProofs.splitRight, portConsCases]

theorem loopRows_inside (body : Code P params (vars ++ before) inside)
    (guard : Port inside .bool) (neg : P [.bool] .bool) (parent : Option (Fin all.length))
    (embed : Embed (vars ++ .count :: .bool :: inside) all) (inner : Rows P params inside all)
    (r : Port inside t) :
    loopRows body guard neg parent embed inner (insideRef vars r) = inner r := by
  simp only [insideRef, loopRows, WhileProofs.splitRight, portConsCases]

/-- A code extension leaves the row of every old reference unchanged. -/
theorem rows_lift (code : Code P params before after) (holes : Rows P params before all)
    (embed : Embed after all) (parent : Option (Fin all.length)) (r : Port before t) :
    code.rows holes embed parent (code.lift r) = holes r := by
  induction code generalizing parent with
  | straight code => exact straightRows_lift code holes embed r
  | seq a b ihA ihB =>
    rw [Code.lift, Code.rows, ihB, ihA]
  | loop init body guard next neg ih =>
    rw [Code.lift, Code.rows, loopRows_inside, ih, loopHoles_right]

abbrev Reads (m : Interpretation.{u,v,w} P) (all : List (Ty Data)) :=
  ∀ {t}, Port all t → Index all.length → Option (m.Value t)

variable (m : Interpretation.{u,v,w} P) (env : Tuple m.Value params)

@[expose] noncomputable def rowValue (r : Row P params all t) (read : Reads m all)
    (i : Index all.length) : Option (m.Value t) :=
  r.label.interpret m env i fun slot j _ => read (r.refs.get (portAt r.inputs slot)) j

/-- Rows indexed by a local port context are the equations at the embedded
ports of the final numbered table. -/
@[expose] def Equations (rows : Rows P params after all) (embed : Embed after all) (read : Reads m all) : Prop :=
  ∀ (i : Index all.length) t (r : Port after t),
    read (embed r) i = rowValue m env (rows r) read i

theorem seqLeft (a : Code P params before vars) (b : Code P params vars after)
    (holes : Rows P params before all) (embed : Embed after all)
    (parent : Option (Fin all.length)) (read : Reads m all)
    (eqs : Equations m env ((Code.seq a b).rows holes embed parent) embed read) :
    Equations m env (a.rows holes (fun r => embed (b.lift r)) parent) (fun r => embed (b.lift r)) read := by
  intro i t r
  have atLift := eqs i t (b.lift r)
  change read (embed (b.lift r)) i = rowValue m env
    (b.rows (a.rows holes (fun q => embed (b.lift q)) parent) embed parent (b.lift r)) read i at atLift
  rw [rows_lift] at atLift
  exact atLift

@[expose] noncomputable def graphRead (code : Code P params [] all)
    {outs : List (Ty Data)} (roots : Tuple (Port all) outs)
    (val : (code.toGraph roots).Valuation m) : Reads m all :=
  fun r i => (numberPort r).read m.carrier (val ((numberPort r).id, i))

theorem graphEquations (code : Code P params [] all)
    {outs : List (Ty Data)} (roots : Tuple (Port all) outs)
    {val : (code.toGraph roots).Valuation m}
    (h : (code.toGraph roots).Solves m env val) :
    Equations m env (code.rows (fun r => nomatch r) (fun r => r) none)
      (fun r => r) (graphRead m code roots val) := by
  intro i t r
  let rows : Rows P params all all := code.rows (fun r => nomatch r) (fun r => r) none
  refine WhileProofs.portForall all (fun t r => graphRead m code roots val r i =
    rowValue m env (rows r) (graphRead m code roots val) i) ?_ t r
  intro j
  have ref : numberPort (portAt all j) = Ref.ofId (code.toGraph roots).sort j := by
    have idEq := Simple.Proofs.number_portAt all j
    generalize numberPort (portAt all j) = r at idEq ⊢
    cases r with
    | mk id ty =>
      change id = j at idEq
      subst id
      rfl
  unfold graphRead
  rw [ref]
  change val (j, i) = _
  rw [h (j, i)]
  unfold Graph.equation Graph.demandStep
  change ((rows (portAt all j)).label.interpret m env i _) = _
  unfold rowValue
  apply congrArg ((rows (portAt all j)).label.interpret m env i)
  funext slot sampled _
  have arg : ((code.toGraph roots).node j).arg slot =
      numberPort ((rows (portAt all j)).refs.get (portAt _ slot)) :=
    Simple.Proofs.get_map _ _ _
  exact congrArg (fun (r : Ref (code.toGraph roots).sort ((code.toGraph roots).node j).inputs[slot]) =>
    r.read m.carrier (val (r.id, sampled))) arg

/-- Pointwise evaluation of straight code in any iteration frame. -/
theorem straightEval (code : Simple.Code P params before after)
    (holes : Rows P params before all) (embed : Embed after all)
    (read : Reads m all) (i : Index all.length) (seed : Simple.Proofs.NodeValues m before)
    (base : ∀ t (r : Port before t), read (embed (code.lift r)) i = seed.get r)
    (eqs : Equations m env (straightRows holes code embed) embed read)
    (t : Ty Data) (r : Port after t) :
    read (embed r) i = (code.eval m env seed).get r := by
  induction code generalizing t with
  | empty => exact base _ r
  | emit prior label refs ih =>
    have earlier := ih (fun r => embed (.tail r)) base (fun j t p => eqs j t (.tail p))
    cases r with
    | tail r => exact earlier _ r
    | head =>
      refine (eqs i _ .head).trans ?_
      change rowValue m env ⟨_, label.map (fun op => op) Fin.elim0, refs.map (fun _ r => embed (.tail r)), none⟩
        read i = emitValue m env label refs (prior.eval m env seed)
      unfold rowValue emitValue
      cases label with
      | param => rfl
      | op | phi => simp only [Label.map, Label.interpret, Simple.Proofs.get_map, earlier]
      | theta impossible | pass impossible | eval impossible => exact impossible.elim0

end Silmaril.SSA.PEG.Simple.Structured.Proofs
