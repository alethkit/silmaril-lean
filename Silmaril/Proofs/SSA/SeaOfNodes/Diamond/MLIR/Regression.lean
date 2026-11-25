module

import Silmaril.SSA.SeaOfNodes.Diamond.MLIR.Thms

namespace Silmaril.SSA.SeaOfNodes.Diamond.MLIR

open RVSDG (Origin Tuple extend)

private abbrev word : ValueSort Unit := .data ()
private abbrev inputs : List (ValueSort Unit) := [.predicate, word]
private abbrev sigs : List (List (Diamond.Ty Unit)) := [[.value word], [.value word]]

private inductive Arithmetic : Diamond.Signature.{0, 0} Unit where
  | inc : Arithmetic [word] word
  | add : Arithmetic [word, word] word

private def arithmetic : Model Arithmetic where
  value _ := Nat
  run
    | .inc, .cons n .nil => Nat.succ n
    | .add, .cons x (.cons y .nil) => Nat.add x y

private abbrev ResultWire := Origin (dataPorts inputs) (extend [] sigs) (.value word)

private def shared : ResultWire := .output (0 : Fin 2) .head
private def doubled : ResultWire := .output (1 : Fin 2) .head

private def diamond (first : Projection) (onFalse : ResultWire) :
    Graph Arithmetic inputs sigs word where
  dataflow :=
    .cons .inc (.cons (.arg (.tail .head)) .nil)
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  predicate := .arg .head
  phi := ⟨⟨first⟩, match first with
    | .onTrue => fun | .first => shared | .second => onFalse
    | .onFalse => fun | .first => onFalse | .second => shared⟩

private def entry (b : Bool) : Tuple (Val arithmetic.value) (dataPorts inputs) :=
  .cons ⟨b⟩ (.cons (4 : Nat) .nil)

-- The two Phi operands are observably different for both predecessor orders.
example : denote arithmetic (diamond .onTrue doubled) (entry true) = (5 : Nat) := rfl
example : denote arithmetic (diamond .onTrue doubled) (entry false) = (10 : Nat) := rfl
example : denote arithmetic (diamond .onFalse doubled) (entry true) = (5 : Nat) := rfl
example : denote arithmetic (diamond .onFalse doubled) (entry false) = (10 : Nat) := rfl

-- Both incoming Phi slots can return the same shared producer.
example : denote arithmetic (diamond .onFalse shared) (entry true) = (5 : Nat) := rfl
example : denote arithmetic (diamond .onFalse shared) (entry false) = (5 : Nat) := rfl

example : (diamond .onFalse doubled).Returns arithmetic (entry false) (10 : Nat) :=
  (returns_iff_denote arithmetic (diamond .onFalse doubled) (entry false) (10 : Nat)).mpr rfl

end Silmaril.SSA.SeaOfNodes.Diamond.MLIR
