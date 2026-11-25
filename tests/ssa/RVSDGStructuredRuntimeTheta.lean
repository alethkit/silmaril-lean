module

import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Thms

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Tests

set_option backward.isDefEq.respectTransparency false

private abbrev T := Ty Unit
private abbrev valuePort : T := .value ()
private abbrev carried : Ports T := [valuePort]
private abbrev results : Ports T := .control 2 :: carried
private abbrev carriedData : Data carried := .value .nil
private abbrev resultData : Data results := .control carriedData

private abbrev PureOp : Dialect Unit PUnit := fun _ _ => Empty

private inductive EffectOp : Dialect Unit PUnit where
  | advance (limit : Option Nat) : EffectOp carried results

private abbrev Op := Opcode PureOp EffectOp

private abbrev model : Model PureOp EffectOp (StateM Nat) where
  value _ := Nat
  runPure op := op.elim
  effect
    | .advance limit, .cons v .nil => fun state =>
      let next := state + 1
      let tag : Fin 2 := match limit with
        | none => 1
        | some limit => if next < limit then 1 else 0
      (.cons ⟨tag⟩ (.cons ((show Nat from v) + 2) .nil), next)

private def inputWires : Wires (Threaded carried) [] carried :=
  .cons (.arg .head) .nil

private def resultWires : Wires (Threaded carried) [Threaded results] results :=
  .cons (.output 0 .head) (.cons (.output 0 (.tail .head)) .nil)

private def body (limit : Option Nat) :
    Term Op (Threaded carried) [] [Threaded results] (Threaded results) :=
  .bind (primitiveNode (.arg (runtimePort carried)) carriedData resultData
    (.effect (EffectOp.advance limit)) inputWires) (fun i => i.elim0)
    (.ret (withRuntime (nextRuntime [] results) resultWires))

private def admitted (limit : Option Nat) : EntryChecked carriedData resultData (body limit) :=
  .bind (.arg (runtimePort carried)) carriedData resultData (.effect (EffectOp.advance limit))
    inputWires (.ret (nextRuntime [] results) resultWires)

private def loop (limit : Option Nat) :
    Loop (P := PureOp) (E := EffectOp) (carried := carried) (sigs := [Threaded results]) :=
  ⟨(body limit).toGraph⟩

private def checked (limit : Option Nat) : BodyChecked carriedData (loop limit) :=
  (admitted limit).collect

private def point (payload state : Nat) : Tuple (RuntimeValues model.value Nat) (Threaded carried) :=
  .cons payload (.cons state .nil)

example : denoteTotal model (loop (some 3)) (checked (some 3)) (point 10 0) =
    _root_.Part.some (point 16 3) :=
  (denoteTotal_eq_some model (loop (some 3)) (checked (some 3)) _ _).mpr
    (.again (next := point 12 1) rfl (.again (next := point 14 2) rfl (.stop rfl)))

-- Even at the stopping state the body runs once and updates both outputs.
example : denoteTotal model (loop (some 3)) (checked (some 3)) (point 10 3) =
    _root_.Part.some (point 12 4) :=
  (denoteTotal_eq_some model (loop (some 3)) (checked (some 3)) _ _).mpr (.stop rfl)

example : denoteTotal model (loop none) (checked none) (point 0 0) = _root_.Part.none := by
  apply (denoteTotal_eq_none model (loop none) (checked none) _).mpr
  exact ⟨fun n => point (Nat.rec 0 (fun _ payload => payload + 2) n) n, rfl, fun _ => rfl⟩

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Theta.Tests
