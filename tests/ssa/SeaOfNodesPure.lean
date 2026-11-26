module

import Silmaril.SSA.SeaOfNodes.Pure.Thms
meta import Silmaril.SSA.SeaOfNodes.Pure.Defs

open Silmaril.SSA.SeaOfNodes
open Diamond (Model ValueSort)

private abbrev byte : ValueSort Unit := .data ()

private inductive ByteOp : List (ValueSort Unit) → ValueSort Unit → Type where
  | one : ByteOp [] byte
  | add : ByteOp [byte, byte] byte

private def byteModel : Model ByteOp where
  value _ := BitVec 8
  run
    | .one, .nil => (1 : BitVec 8)
    | .add, .cons x (.cons y .nil) => BitVec.add x y

-- Vertex 0 produces 1, vertex 1 produces x + 1, and vertex 2 reads vertex 1 twice.
private def doubledNext : Pure.Program ByteOp [byte] byte where
  dataflow :=
    .cons .one .nil <|
    .cons .add (.cons (.arg .head) (.cons (.output ⟨0, by decide⟩ .head) .nil)) <|
    .cons .add (.cons (.output ⟨1, by decide⟩ .head) (.cons (.output ⟨1, by decide⟩ .head) .nil)) .nil
  result := .output ⟨2, by decide⟩ .head

/-- info: 42 -/
#guard_msgs in
#eval (doubledNext.eval byteModel (.cons (20 : BitVec 8) .nil)).toNat

/-- info: 0 -/
#guard_msgs in
#eval (doubledNext.eval byteModel (.cons (255 : BitVec 8) .nil)).toNat

example (x : BitVec 8) :
    doubledNext.lower.run (Pure.toRVSDGModel byteModel) (.cons x .nil) =
      .cons ((x + 1) + (x + 1)) .nil :=
  doubledNext.lower_run byteModel (.cons x .nil)

-- Both lowered operands still refer to the same numbered producer.
example : ((doubledNext.lower.nodes (2 : Fin 3)).inputs.get .head).producer = some 1 := rfl
example : ((doubledNext.lower.nodes (2 : Fin 3)).inputs.get (.tail .head)).producer = some 1 := rfl

private def input : Pure.Program ByteOp [byte] byte :=
  ⟨.nil, .arg .head⟩

private def inputWithUnusedOne : Pure.Program ByteOp [byte] byte :=
  ⟨.cons .one .nil .nil, .arg .head⟩

private def valid : Pure.Equation ByteOp [byte] byte := ⟨input, inputWithUnusedOne⟩

example : valid.toRVSDG.Holds (Pure.toRVSDGModel byteModel) :=
  (valid.satisfaction byteModel).mpr (fun _ => rfl)

private def invalid : Pure.Equation ByteOp [byte] byte := ⟨doubledNext, input⟩

example : ¬ invalid.toRVSDG.Holds (Pure.toRVSDGModel byteModel) := by
  intro holds
  have result := (invalid.satisfaction byteModel).mp holds (.cons (20 : BitVec 8) .nil)
  change (42 : BitVec 8) = 20 at result
  exact (by decide : (42 : BitVec 8) ≠ 20) result
