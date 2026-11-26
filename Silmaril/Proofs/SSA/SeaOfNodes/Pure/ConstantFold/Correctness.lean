module

public import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Scan
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open GVN.Elimination (read_splitOrigin splitOrigin)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {Op : Signature Unit} {m : Model Op}
variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {ins : List (ValueSort Unit)} {out : ValueSort Unit}
variable {entry : Tuple (Val m.value) args}
variable {locals : Locals (Val m.value) past} {known : Literals m args past}

private def Agrees (known : Literals m args past) (entry : Tuple (Val m.value) args)
    (locals : Locals (Val m.value) past) : Prop :=
  ∀ {t : Ty Unit} (wire : Origin args past t) {value}, known wire = some value →
    Diamond.read m wire entry locals = value

private theorem push_agrees (agree : Agrees known entry locals)
    {actual : Val m.value (.value out)} {hint : Option (Val m.value (.value out))}
    (sound : ∀ value, hint = some value → actual = value) :
    Agrees (known.push hint) entry (locals.snoc (.cons actual .nil)) := by
  intro t wire value found
  have read := read_splitOrigin wire m entry locals (.cons actual .nil)
  cases part : splitOrigin (T := Ty Unit) (past := past) [.value out] wire with
  | inl earlier =>
    simp only [Literals.push, part] at found
    exact (by simpa only [part] using read.symm : Diamond.read m wire entry _ =
      Diamond.read m earlier entry locals).trans (agree earlier found)
  | inr port =>
    cases port with
    | head =>
      simp only [Literals.push, part] at found
      exact (by simpa only [part, Tuple.get] using read.symm : Diamond.read m wire entry _ =
        actual).trans (sound value found)
    | tail rest => nomatch rest

private theorem literalInputs_sound (agree : Agrees known entry locals) {ports : List (Ty Unit)}
    (operands : Wires args past ports) {values : Tuple (Val m.value) ports}
    (found : literalInputs? known operands = some values) :
    operands.read entry locals = values := by
  induction operands with
  | nil =>
    cases Option.some.inj found
    rfl
  | cons wire rest ih =>
    obtain ⟨value, knownWire, result⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨tail, knownRest, rfl⟩ := Option.map_eq_some_iff.mp result
    change Tuple.cons (Diamond.read m wire entry locals) (Wires.read rest entry locals) = _
    rw [agree wire knownWire, ih knownRest]

private theorem replacement_sound (agree : Agrees known entry locals) {op : Op ins out}
    (rule : Rule m op) (operands : Wires args past (dataPorts ins)) {literal : Op [] out}
    (found : rule.replacement? known operands = some literal) :
    m.run op (operands.read entry locals) = m.run literal .nil := by
  cases rule with
  | literal original =>
    cases operands
    cases Option.some.inj found
    rfl
  | operation opcode encode read_encode =>
    obtain ⟨values, knownOperands, rfl⟩ := Option.map_eq_some_iff.mp found
    rw [read_encode, literalInputs_sound agree operands knownOperands]

private theorem dataflow_eval (rules : Rules m) (flow : Dataflow Op args past sigs)
    (agree : Agrees known entry locals) :
    (foldDataflow rules known flow).eval m entry locals = flow.eval m entry locals := by
  induction flow with
  | nil => rfl
  | @cons scope sigs ins out op operands rest ih =>
    cases found : (rules op).replacement? known operands with
    | none =>
      simp only [foldDataflow, found, Dataflow.eval]
      exact ih (push_agrees agree (by intro value impossible; cases impossible))
    | some literal =>
      have same := replacement_sound agree (rules op) operands found
      simp only [foldDataflow, found, Dataflow.eval]
      calc
        _ = rest.eval m entry (locals.snoc (.cons (m.run literal .nil) .nil)) :=
          ih (push_agrees agree (fun _ foundValue => Option.some.inj foundValue))
        _ = _ := congrArg (fun value : Val m.value (.value out) =>
          rest.eval m entry (locals.snoc (.cons value .nil))) same.symm

theorem program_locals_eq {inputs : List (ValueSort Unit)} (rules : Rules m)
    (program : Program Op inputs out) (entry : Tuple (Val m.value) (dataPorts inputs)) :
    (fold rules program).dataflow.eval m entry PUnit.unit = program.dataflow.eval m entry PUnit.unit :=
  dataflow_eval (past := []) rules program.dataflow (entry := entry) (locals := PUnit.unit)
    (known := fun _ => none) (by intro t wire value impossible; cases impossible)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold
