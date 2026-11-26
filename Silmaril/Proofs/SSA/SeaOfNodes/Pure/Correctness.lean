module

public import Silmaril.SSA.SeaOfNodes.Pure.Defs
import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.Proofs

open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs : List (ValueSort Data)} {out : ValueSort Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}

private theorem eval_lowerDataflow (m : Model.{u, v, w} Op) (flow : Dataflow Op args past sigs)
    (result : Origin args (extend past sigs) (.value out))
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past) :
    (lowerDataflow flow result).eval (toRVSDGModel m) entry locals =
      .cons (Diamond.read m result entry (flow.eval m entry locals)) .nil := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => exact ih result _

theorem lower_run (p : Program Op inputs out) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) (dataPorts inputs)) :
    p.lower.run (toRVSDGModel m) entry = .cons (p.eval m entry) .nil := by
  rw [Program.lower, RVSDG.Term.run_toGraph]
  exact eval_lowerDataflow m p.dataflow p.result entry PUnit.unit

theorem satisfaction (e : Equation Op inputs out) (m : Model.{u, v, w} Op) :
    e.toRVSDG.Holds (toRVSDGModel m) ↔ e.Holds m := by
  change (∀ entry, e.lhs.lower.run (toRVSDGModel m) entry =
    e.rhs.lower.run (toRVSDGModel m) entry) ↔ e.Holds m
  simp only [lower_run, Equation.Holds]
  constructor
  · intro holds entry
    exact congrArg (fun xs => xs.get .head) (holds entry)
  · intro holds entry
    rw [holds entry]

end Silmaril.SSA.SeaOfNodes.Pure.Proofs
