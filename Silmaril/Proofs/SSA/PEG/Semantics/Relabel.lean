module

public import Silmaril.Proofs.SSA.PEG.Semantics.Demand
public import Silmaril.Proofs.SSA.PEG.Semantics.Equations

public section

namespace Silmaril.SSA.PEG.Semantics.Proofs

open RVSDG (Tuple)

universe u v w x

variable {Data : Type u} {P : InstructionSet.{u,v} Data} {Q : InstructionSet.{u,w} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {m : Interpretation.{u,w,x} Q}

private theorem interpret_mapOps {ins : List (Ty Data)} {out : Ty Data}
    (label : Label P params (Fin l) ins out) (f : InstructionMap P Q)
    (env : Tuple m.Value params) (i : Index l)
    (read : ∀ (slot : Fin ins.length), Index l → Option (m.Value ins[slot])) :
    (label.map f id).interpret m env i (fun slot j _ => read slot j) =
      label.interpret (m.reduct f) env i (fun slot j _ => read slot j) := by
  cases label <;> simp [Label.map, Label.interpret]

private theorem ref_reindex_refl {s : Fin n → Ty Data} {out : Ty Data} (r : Ref s out) :
    r.reindex (Equiv.refl _) = r := by cases r; rfl

set_option backward.isDefEq.respectTransparency false in
theorem equation_mapOps (f : InstructionMap P Q) (env : Tuple m.Value params)
    (values : g.Valuation (m.reduct f)) (q : Request n l) :
    (g.mapOps f).equation m env values q = g.equation (m.reduct f) env values q := by
  let node := g.node q.1
  let mapped := node.relabel f (Equiv.refl _) (Equiv.refl _)
  have args (slot : Fin node.inputs.length) : mapped.arg slot = node.arg slot :=
    (node.arg_relabel f _ _ slot).trans (ref_reindex_refl _)
  let read (slot : Fin node.inputs.length) (j : Index l) :=
    (node.arg slot).read m.carrier (values ((node.arg slot).id, j))
  calc
    _ = mapped.label.interpret m env q.2 (fun slot j _ => read slot j) := by
      apply congrArg (mapped.label.interpret m env q.2)
      funext slot j _
      exact congrArg (fun r => r.read m.carrier (values (r.id, j))) (args slot)
    _ = _ := interpret_mapOps node.label f env q.2 read

set_option backward.isDefEq.respectTransparency false in
theorem denote_mapOps (f : InstructionMap P Q) (env : Tuple m.Value params)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapOps f).Demand) :
    (g.mapOps f).denote m env mapped = g.denote (m.reduct f) env wf := by
  refine solves_unique (g := g) (m := m.reduct f) (env := env) wf ?_ (denote_solves wf)
  intro q
  exact (denote_solves mapped q).trans (equation_mapOps f env _ q)

private theorem observeTuple_reindex_refl {s : Fin n → Ty Data} {ts : List (Ty Data)}
    (rs : Tuple (Ref s) ts) (f : InstructionMap P Q)
    (values : ∀ q : Request n l, Option (m.Value (s q.1))) (i : Index l) :
    (rs.map (fun _ r => r.reindex (Equiv.refl _))).map
        (fun _ r => r.read m.carrier (values (r.id, i))) =
      rs.map (fun _ r => r.read (m.reduct f).carrier (values (r.id, i))) := by
  induction rs with
  | nil => rfl
  | cons r _ ih =>
    have head : (r.reindex (Equiv.refl _)).read m.carrier (values (r.id, i)) =
        r.read (m.reduct f).carrier (values (r.id, i)) := by cases r; rfl
    exact congrArg₂ Tuple.cons head ih

theorem observe_denote_mapOps (f : InstructionMap P Q) (env : Tuple m.Value params)
    (wf : WellFounded g.Demand) (mapped : WellFounded (g.mapOps f).Demand) (i : Index l) :
    (g.mapOps f).observe m ((g.mapOps f).denote m env mapped) i =
      g.observe (m.reduct f) (g.denote (m.reduct f) env wf) i := by
  rw [denote_mapOps f env wf mapped]
  exact observeTuple_reindex_refl g.roots f _ i

end Silmaril.SSA.PEG.Semantics.Proofs
