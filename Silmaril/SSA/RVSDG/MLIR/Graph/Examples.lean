module

import Silmaril.SSA.RVSDG.MLIR.Graph.Thms

/-! A numbered graph sends a producer's result into two isolated γ arms.
The selected arm supplies both returned slots. -/

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Examples

private abbrev data : Ty Unit := .value ()
private abbrev selector : Ty Unit := .control 2

private inductive Primitive : Dialect Unit Empty where
  | inc : Primitive [data] [data]
  | twice : Primitive [data] [data]

private abbrev source : Source Unit := ⟨Primitive⟩

private def runtime : Model.{0, 0, 0} source.op where
  value _ := Nat
  state s := s.elim
  run
    | .inc, .cons x .nil => .cons (Nat.add x 1) .nil
    | .twice, .cons x .nil => .cons (Nat.mul 2 x) .nil

private def arm (op : Primitive [data] [data]) : Term source.op [data] [] [[data]] [data] :=
  .bind ⟨[data], .simple op, .cons (.arg .head) .nil, Fin.elim0⟩
    (fun r => Fin.elim0 (show Fin 0 from r))
    (.ret (.cons (.output ⟨0, by decide⟩ .head) .nil))

private def producer : Node source.op [selector, data] [] [data] :=
  ⟨[data], .simple .inc, .cons (.arg (.tail .head)) .nil, Fin.elim0⟩

private def branch : Node source.op [selector, data] [[data]] [data] :=
  ⟨[selector, data], .gamma 0, .cons (.arg .head) (.cons (.output 0 .head) .nil),
    fun _ => [[data]]⟩

private def graph : RVSDG.Graph source.op [selector, data] [] [[data], [data]] [data, data] :=
  (Term.bind producer (fun r => Fin.elim0 (show Fin 0 from r))
    (.bind branch
      (fun r => if (show Fin 2 from r) = 0 then arm .inc else arm .twice)
      (.ret (.cons (.output ⟨1, by decide⟩ .head)
        (.cons (.output ⟨1, by decide⟩ .head) .nil))))).toGraph

private def input (choice : Fin 2) : Tuple runtime.Val [selector, data] :=
  .cons ⟨choice⟩ (.cons (4 : Nat) .nil)

example : (lower graph 0).denote (model runtime) (toAssignment (input 0)) = (6 : Nat) := rfl
example : (lower graph 1).denote (model runtime) (toAssignment (input 1)) = (10 : Nat) := rfl

example (choice : Fin 2) :
    ofAssignment [data, data] (fun i =>
      (lower graph i).denote (model runtime) (toAssignment (input choice))) =
      graph.run runtime (input choice) :=
  denote_lower runtime graph (input choice)

end Silmaril.SSA.RVSDG.MLIR.Graph.Examples
