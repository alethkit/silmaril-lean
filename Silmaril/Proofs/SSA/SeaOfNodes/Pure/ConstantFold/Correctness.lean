module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open SubZero (BinaryOpcode model word)
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN.Elimination (read_splitOrigin splitOrigin)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val model.value) args}
variable {locals : Locals (Val model.value) past} {known : Literals args past}

private def Agrees (known : Literals args past) (entry : Tuple (Val model.value) args)
    (locals : Locals (Val model.value) past) : Prop :=
  ∀ {t : Ty Unit} (wire : Origin args past t) {value}, known wire = some value →
    Diamond.read model wire entry locals = value

private theorem push_agrees (agree : Agrees known entry locals)
    {actual : Val model.value (.value out)} {hint : Option (Val model.value (.value out))}
    (sound : ∀ value, hint = some value → actual = value) :
    Agrees (known.push hint) entry (locals.snoc (.cons actual .nil)) := by
  intro t wire value found
  have read := read_splitOrigin wire model entry locals (.cons actual .nil)
  cases part : splitOrigin (T := Ty Unit) (past := past) [.value out] wire with
  | inl earlier =>
    simp only [Literals.push, part] at found
    exact (by simpa only [part] using read.symm : Diamond.read model wire entry _ =
      Diamond.read model earlier entry locals).trans (agree earlier found)
  | inr port =>
    cases port with
    | head =>
      simp only [Literals.push, part] at found
      exact (by simpa only [part, Tuple.get] using read.symm : Diamond.read model wire entry _ =
        actual).trans (sound value found)
    | tail rest => nomatch rest

private theorem binaryLiteral_sound (agree : Agrees known entry locals) (op : BinaryOpcode)
    (operands : Wires args past (dataPorts [word, word])) {literal : SubZero.Opcode [] word}
    (found : binaryLiteral? known op operands = some literal) :
    model.run op (operands.read entry locals) = model.run literal .nil := by
  cases operands with
  | cons lhs tail =>
    cases tail with
    | cons rhs empty =>
      cases empty
      obtain ⟨left, knownLeft, result⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨right, knownRight, rfl⟩ := Option.map_eq_some_iff.mp result
      change model.run op (.cons (Diamond.read model lhs entry locals)
        (.cons (Diamond.read model rhs entry locals) .nil)) = _
      rw [agree lhs knownLeft, agree rhs knownRight]
      rfl

private theorem literal_sound (agree : Agrees known entry locals) (op : SubZero.Opcode ins out)
    (operands : Wires args past (dataPorts ins)) {literal : SubZero.Opcode [] out}
    (found : literal? known op operands = some literal) :
    model.run op (operands.read entry locals) = model.run literal .nil := by
  cases op with
  | literal value =>
    cases operands
    cases Option.some.inj found
    rfl
  | add | sub | mul => exact binaryLiteral_sound agree _ operands found

private theorem dataflow_eval (flow : Dataflow SubZero.Opcode args past sigs)
    (agree : Agrees known entry locals) :
    (foldDataflow known flow).eval model entry locals = flow.eval model entry locals := by
  induction flow with
  | nil => rfl
  | @cons scope sigs ins out op operands rest ih =>
    cases found : literal? known op operands with
    | none =>
      simp only [foldDataflow, found, Dataflow.eval]
      exact ih (push_agrees agree (by intro value impossible; cases impossible))
    | some literal =>
      have same := literal_sound agree op operands found
      simp only [foldDataflow, found, Dataflow.eval]
      calc
        _ = rest.eval model entry (locals.snoc (.cons (model.run literal .nil) .nil)) :=
          ih (push_agrees agree (fun _ foundValue => Option.some.inj foundValue))
        _ = _ := congrArg (fun value : Val model.value (.value out) =>
          rest.eval model entry (locals.snoc (.cons value .nil))) same.symm

theorem program_locals_eq {inputs : List (ValueSort Unit)} (program : Program SubZero.Opcode inputs out)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (fold program).dataflow.eval model entry PUnit.unit = program.dataflow.eval model entry PUnit.unit :=
  dataflow_eval (past := []) program.dataflow (entry := entry) (locals := PUnit.unit)
    (known := fun _ => none) (by intro t wire value impossible; cases impossible)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold
