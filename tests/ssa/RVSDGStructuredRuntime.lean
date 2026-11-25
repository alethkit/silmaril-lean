module

import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

namespace Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Tests

set_option backward.isDefEq.respectTransparency false

private abbrev T := Ty Unit
private abbrev val : T := .value ()
private abbrev root : Ports T := [.control 3, val, val]
private abbrev single : Ports T := [val]
private abbrev pair : Ports T := [val, val]
private abbrev triple : Ports T := [val, val, val]
private abbrev rootData : Data root := .control (.value (.value .nil))
private abbrev singleData : Data single := .value .nil
private abbrev pairData : Data pair := .value (.value .nil)
private abbrev tripleData : Data triple := .value (.value (.value .nil))
private abbrev vertex : Ports T := Threaded single

private inductive PureOp : Dialect Unit PUnit where
  | first : PureOp pair single

private inductive EffectOp : Dialect Unit PUnit where
  | prefix : EffectOp single single
  | branch (digit : Nat) : EffectOp pair single
  | suffix : EffectOp triple single

private abbrev Op := Opcode PureOp EffectOp

private abbrev model : Model PureOp EffectOp (StateM Nat) where
  value _ := Nat
  runPure
    | .first, .cons x (.cons _ .nil) => .cons x .nil
  effect
    | .prefix, .cons x .nil => fun state => (.cons ((show Nat from x) + 1) .nil, state * 10 + 1)
    | .branch digit, .cons x (.cons y .nil) => fun state =>
      (.cons ((show Nat from x) + (show Nat from y)) .nil, state * 10 + digit)
    | .suffix, .cons x (.cons y (.cons z .nil)) => fun state =>
      (.cons ((show Nat from x) + (show Nat from y) + (show Nat from z)) .nil, state * 10 + 4)

private def armOp : Fin 3 → Instruction PureOp EffectOp pair single :=
  Fin.cases (.pure .first) (fun j => .effect (.branch (j.val + 2)))

private def armInputs : Wires (Threaded pair) [] pair :=
  .cons (.arg .head) (.cons (.arg (.tail .head)) .nil)

private def armResult : Wires (Threaded pair) [vertex] single :=
  .cons (.output 0 .head) .nil

private def arm (j : Fin 3) : Term Op (Threaded pair) [] [vertex] vertex :=
  .bind (primitiveNode (.arg (runtimePort pair)) pairData singleData (armOp j) armInputs)
    (fun i => i.elim0)
    (.ret (withRuntime (nextRuntime [] single) armResult))

private def armChecked (j : Fin 3) : EntryChecked pairData singleData (arm j) :=
  .bind (.arg (runtimePort pair)) pairData singleData (armOp j) armInputs
    (.ret (nextRuntime [] single) armResult)

private def prefixInputs : Wires (Threaded root) [] single :=
  .cons (.arg (.tail .head)) .nil

-- The result of vertex zero supplies both payload inputs of γ.
private def gammaInputs : Wires (Threaded root) [vertex] pair :=
  .cons (.output 0 .head) (.cons (.output 0 .head) .nil)

-- The suffix reads one argument, the selected result, and a pre-γ result.
private def suffixInputs : Wires (Threaded root) [vertex, vertex] triple :=
  .cons (.arg (.tail .head)) (.cons (.output 1 .head) (.cons (.output 0 .head) .nil))

private def result : Wires (Threaded root) [vertex, vertex, vertex] single :=
  .cons (.output 2 .head) .nil

private def program : Term Op (Threaded root) [] [vertex, vertex, vertex] vertex :=
  .bind (primitiveNode (.arg (runtimePort root)) singleData singleData (.effect EffectOp.prefix) prefixInputs)
    (fun i => i.elim0) <|
  .bind (gammaNode (out := single) 1 (.arg .head) (nextRuntime [] single) gammaInputs
    (fun _ => [vertex])) arm <|
  .bind (primitiveNode (nextRuntime [vertex] single) tripleData singleData (.effect EffectOp.suffix) suffixInputs)
    (fun i => i.elim0) <|
  .ret (withRuntime (nextRuntime [vertex, vertex] single) result)

private def admitted : EntryChecked rootData singleData program :=
  .bind (a := rootData) (b := singleData) (.arg (runtimePort root)) singleData singleData (.effect EffectOp.prefix) prefixInputs <|
  .gamma 1 (.arg (.head : Port (Threaded root) (.control 3))) (nextRuntime [] single) pairData singleData gammaInputs (fun _ => [vertex])
    armChecked <|
  .bind (nextRuntime [vertex] single) tripleData singleData (.effect EffectOp.suffix) suffixInputs <|
  .ret (nextRuntime [vertex, vertex] single) result

private def inputs (j : Fin 3) : Tuple (Values model.value) root :=
  .cons ⟨j⟩ (.cons (5 : Nat) (.cons (99 : Nat) .nil))

example : (admitted.denote model (inputs 0)).run 0 = (.cons (17 : Nat) .nil, 14) := rfl
example : (admitted.denote model (inputs 1)).run 0 = (.cons (23 : Nat) .nil, 124) := rfl
example : (admitted.denote model (inputs 2)).run 0 = (.cons (23 : Nat) .nil, 134) := rfl

example : denoteGraph model program.toGraph admitted.collect = admitted.denote model :=
  denote_toGraph model admitted

private def entry : Tuple (RuntimeValues model.value Nat) (Threaded root) :=
  .cons ⟨1⟩ (.cons (5 : Nat) (.cons (99 : Nat) (.cons (0 : Nat) .nil)))

example : program.toGraph.run model.toRVSDG entry = .cons (23 : Nat) (.cons (124 : Nat) .nil) := by
  rw [← denoteGraph_run model program.toGraph admitted.collect entry, denote_toGraph model admitted]
  rfl

end Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Tests
