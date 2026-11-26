module

public import Silmaril.SSA.PEG.Bridge.LambdaSSA.Defs
public import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.LambdaSSA.Proofs

open RVSDG (Port Tuple)
open Simple (Code select emitValue phiNodes)
open Source

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params before middle after ins results : List (Ty Data)} {t : Ty Data}

theorem get_map {F G : Ty Data → Type} (xs : Tuple F before) (f : ∀ t, F t → G t)
    (p : Port before t) : (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail p ih => cases xs with | cons _ xs => exact ih xs

variable (m : Interpretation.{0,0,0} P) (input : Tuple m.Value params)

abbrev Values (m : Interpretation.{0,0,0} P) := Tuple (fun t => Option (m.Value t))

private theorem eval_append (first : Code P params before middle) (last : Code P params middle after)
    (base : Values m before) :
    (first.append last).eval m input base = last.eval m input (first.eval m input base) := by
  induction last with
  | empty => rfl
  | emit _ _ _ ih => simp only [Code.append, Code.eval, ih]

private theorem eval_lift (code : Code P params before after) (base : Values m before)
    (p : Port before t) : (code.eval m input base).get (code.lift p) = base.get p := by
  induction code with
  | empty => rfl
  | emit _ _ _ ih => exact ih

private theorem eval_rebase (f : Renaming before middle) (code : Code P params before after)
    (xs : Values m before) (ys : Values m middle)
    (agree : ∀ {t} (p : Port before t), ys.get (f p) = xs.get p) (p : Port after t) :
    let rebased := rebase f code
    (rebased.2.1.eval m input ys).get (rebased.2.2 p) = (code.eval m input xs).get p := by
  induction code generalizing t with
  | empty => exact agree p
  | emit prior label refs ih =>
    cases p with
    | head =>
      dsimp only [rebase, Code.eval, Renaming.push, Tuple.get]
      unfold emitValue
      apply congrArg (label.interpret m input Simple.Index.zero)
      funext slot j access
      rw [get_map]
      exact ih (refs.get (portAt _ slot))
    | tail p => exact ih p

private theorem select_rebase (f : Renaming before after) (xs : Values m before)
    (ys : Values m after) (agree : ∀ {t} (p : Port before t), ys.get (f p) = xs.get p)
    (refs : Tuple (Port before) results) :
    select ys (refs.map fun _ p => f p) = select xs refs := by
  induction refs with
  | nil => rfl
  | cons p refs ih => exact congrArg₂ Tuple.cons (agree p) ih

private theorem eval_phi (condition : Port before .bool) (yes no : Tuple (Port before) results)
    (xs : Values m before) (flag : ULift Bool) (test : xs.get condition = some flag) :
    let join := phiNodes (P := P) (params := params) condition yes no
    select (join.code.eval m input xs) join.refs =
      if flag.down then select xs yes else select xs no := by
  induction yes with
  | nil => cases no; cases flag.down <;> rfl
  | cons y ys ih =>
    cases no with
    | cons n ns =>
      let rest := phiNodes (P := P) (params := params) condition ys ns
      let values := rest.code.eval m input xs
      let value := emitValue m input .phi
        (.cons (rest.code.lift condition) (.cons (rest.code.lift y) (.cons (rest.code.lift n) .nil)))
        values
      have head : value = (if flag.down then xs.get y else xs.get n) := by
        change (values.get (rest.code.lift condition)).elim none
          (fun b => if b.down then values.get (rest.code.lift y) else values.get (rest.code.lift n)) = _
        simp only [values, eval_lift, test, Option.elim]
      have tail : select (.cons value values) (rest.refs.map fun _ p => Port.tail p) =
          select values rest.refs :=
        select_rebase m (fun p => .tail p) values _ (fun _ => rfl) rest.refs
      change Tuple.cons (F := fun t => Option (m.Value t)) value (select (.cons value values) (rest.refs.map fun _ p => Port.tail p)) = _
      rw [tail, head, ih ns]
      cases flag.down <;> rfl

theorem observe_source (g : ScopedDiamond P params results) (wf : WellFounded g.toPEG.Demand)
    (idx : Index 0) (flag : ULift Bool)
    (test : (g.sharedCode.eval m input .nil).get g.guard = some flag) :
    g.toPEG.observe m (g.toPEG.denote m input wf) idx =
      if flag.down then
        select (g.onTrue.code.eval m input (g.sharedCode.eval m input .nil)) g.onTrue.outputs
      else
        select (g.onFalse.code.eval m input (g.sharedCode.eval m input .nil)) g.onFalse.outputs := by
  let shared := g.sharedCode.eval m input .nil
  let left := g.onTrue.code.eval m input shared
  let right := rebase g.onTrue.code.lift g.onFalse.code
  let both := right.2.1.eval m input left
  have guard_eq : both.get (right.2.1.lift (g.onTrue.code.lift g.guard)) = some flag :=
    (eval_lift m input right.2.1 left _).trans ((eval_lift m input g.onTrue.code shared _).trans test)
  have left_eq : select both (right.2.1.liftRefs g.onTrue.outputs) = select left g.onTrue.outputs :=
    select_rebase m (fun p => right.2.1.lift p) left both
      (eval_lift m input right.2.1 left) g.onTrue.outputs
  have right_eq : select both (g.onFalse.outputs.map fun _ p => right.2.2 p) =
      select (g.onFalse.code.eval m input shared) g.onFalse.outputs :=
    select_rebase m (fun p => right.2.2 p) _ both
      (eval_rebase m input g.onTrue.code.lift g.onFalse.code shared left
        (eval_lift m input g.onTrue.code shared)) g.onFalse.outputs
  refine (Code.observe_toGraph (Source.build g).code (Source.build g).refs m input wf idx).trans ?_
  simp only [Source.build, eval_append]
  rw [eval_phi m input _ _ _ both flag guard_eq, left_eq, right_eq]

end Silmaril.SSA.PEG.Bridge.LambdaSSA.Proofs
