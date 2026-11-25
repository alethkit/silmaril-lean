module

import Silmaril.SSA.RVSDG.Theta.Categorical.Thms

namespace Silmaril.SSA.RVSDG.Theta.CategoricalTests

private abbrev Ty := PortType Unit Unit
private abbrev carried : Ports Ty := [.state ()]
private abbrev results := BodyResults carried

private inductive Op : Dialect Unit Unit where
  | update (limit : Option Nat) : Op carried results

private def model : Model Op where
  value _ := Unit
  state _ := Nat
  run
    | .update limit, .cons n .nil =>
      let updated := Nat.succ n
      let again := match limit with
        | none => true
        | some limit => decide (updated < limit)
      .cons (⟨if again then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons updated .nil)

private def values (n : Nat) : Tuple model.Val carried := .cons n .nil

private def loop (limit : Option Nat) : Graph Op carried [results] :=
  let node : Node Op carried [] results :=
    ⟨carried, .simple (.update limit), .cons (.arg .head) .nil, fun i => i.elim0⟩
  ⟨(RVSDG.Term.bind node (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head)
      (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))).toGraph⟩

example : (loop (some 3)).denotePart model (values 0) = Part.some (Categorical.pack (values 3)) :=
  ((loop (some 3)).denotePart_eq_some model _ _).2
    (.again (next := values 1) rfl (.again (next := values 2) rfl (.stop rfl)))

-- A body step still runs when the initial value already reaches the bound.
example : (loop (some 3)).denotePart model (values 3) = Part.some (Categorical.pack (values 4)) :=
  ((loop (some 3)).denotePart_eq_some model _ _).2 (.stop rfl)

example : (loop none).denotePart model (values 0) = Part.none :=
  ((loop none).denotePart_eq_none model _).2 ⟨values, rfl, fun _ => rfl⟩

end Silmaril.SSA.RVSDG.Theta.CategoricalTests
