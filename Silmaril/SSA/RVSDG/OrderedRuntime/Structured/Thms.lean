module

public import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Defs
public import Silmaril.SSA.RVSDG.Thms
import Silmaril.Proofs.SSA.RVSDG.OrderedRuntime.Structured.Adequacy

/-! # Term/graph correspondence and deterministic state adequacy -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}

/-- Numbering preserves the admission witness for an inductive region. -/
def Checked.collect {a : Data args} {b : Data outs}
    {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) : EntryChecked a b t.toGraph.toTerm :=
  (Term.toTerm_toGraph t).symm ▸ checked

/-- Collecting the term has no effect on the computation denoted by it. -/
theorem denote_toGraph {M : Type (max u w) → Type (max u w)} [Monad M] (m : Model P E M)
    {a : Data args} {b : Data outs} {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked a b t) :
    denoteGraph m t.toGraph checked.collect = checked.denote m :=
  Proofs.denote_transport m (Term.toTerm_toGraph t) checked

variable {ρ : Type (max u w)} (m : Model P E (StateM ρ))

/-- The monadic and explicit-wire folds agree at every typed prefix. -/
theorem eval_run {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value ρ) (Threaded args))
    (locals : Locals (RuntimeValues m.value ρ) past) :
    decode ((checked.eval m (eraseTuple entry) (eraseLocals past locals)).run
      (readOrigin live entry locals)) = t.eval m.toRVSDG entry locals :=
  Proofs.eval_agrees m checked entry locals

/-- The graph computation returns exactly the explicit numbered graph's
data and final runtime, starting from any entry tuple. -/
theorem denoteGraph_run {a : Data args} {b : Data outs}
    (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked a b g.toTerm)
    (input : Tuple (RuntimeValues m.value ρ) (Threaded args)) :
    decode ((denoteGraph m g checked (eraseTuple (splitRuntime args input).1)).run
      (splitRuntime args input).2) = g.run m.toRVSDG input :=
  Proofs.denote_agrees m g checked input

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured
