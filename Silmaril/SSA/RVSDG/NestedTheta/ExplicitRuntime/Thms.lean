module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.OrderedState.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Agreement

/-! # Finite observations of the explicit and implicit nested runtime -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime

open OrderedRuntime
open Structured (Data Opcode Threaded RuntimeValues runtime readOrigin eraseTuple eraseLocals)

universe u v w
variable {V : Type u} {P E : Dialect.{u, v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Structured.Ty V)} {past sigs : List (Ports (Structured.Ty V))}

/-- The typed numbering round trip transports closed admission witnesses. -/
def Checked.collect {a : Data args} {b : Data outs}
    {t : Term (Opcode P E) (Threaded args) [] sigs (Threaded outs)}
    (checked : EntryChecked (a := a) (b := b) t) : EntryChecked (a := a) (b := b) t.toGraph.toTerm :=
  (Term.toTerm_toGraph t).symm ▸ checked

/-- A return contains exactly one token. The erased tuple and the separately
observed token determine the original tuple and represent every implicit result. -/
theorem boundaryResult_bijective {value : V → Type (max u w)} (data : Data outs) :
    Function.Bijective (boundaryResult (value := value) (σ := σ) (outs := outs)) :=
  Proofs.boundary_bijective data

/-- At each open prefix the designated live wire supplies the initial state.
The unbounded finite derivations agree on all data and on the returned token. -/
theorem Checked.exec_iff (m : Structured.Model P E (StateM σ))
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    t.Exec m.toRVSDG entry locals output ↔
      OrderedState.exec (erasedModel m) checked.erase (eraseTuple entry) (eraseLocals past locals)
        (readOrigin live entry locals) (boundaryResult output) :=
  Proofs.exec_iff m checked entry locals output

set_option backward.isDefEq.respectTransparency false in
/-- Every finite explicit graph result is observed by ordered StateT after
erasure, and each such observation reflects a finite explicit return. -/
theorem observe_eq_some (m : Structured.Model P E (StateM σ))
    {a : Data args} {b : Data outs} (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
    (checked : EntryChecked (a := a) (b := b) g.toTerm)
    (input : Tuple (RuntimeValues m.value σ) (Threaded args))
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    observe m g checked input = _root_.Part.some (boundaryResult output) ↔ g.Returns m.toRVSDG input output := by
  rw [observe, OrderedState.observe_eq_some, Term.toTerm_toGraph, Graph.returns_iff]
  exact (checked.exec_iff m input PUnit.unit output).symm

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime
