module

public import Silmaril.SSA.SeaOfNodes.Pure.SubSelf.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.SubSelf
open SubZero (model operands? operandsFor? word wordPort)
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (operandScope)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {flow : Dataflow SubZero.Opcode args past sigs}

private theorem same_origin {t : Ty Unit} (lhs rhs : Origin args past t)
    (same : lhs.address = rhs.address) : lhs = rhs :=
  congrArg (fun (wires : Wires args past [t]) => wires.get .head)
    (Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective (.cons lhs .nil) (.cons rhs .nil)
      (congrArg (fun address => [address]) same))

private theorem replace_eval (candidate : Producer flow word)
    (wire : Origin args (operandScope candidate) wordPort)
    (operands : operands? candidate = some (wire, wire))
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    (replaceWithZero candidate).eval model entry locals = flow.eval model entry locals := by
  induction flow with
  | nil => cases candidate
  | @cons scope sigs ins out opcode edges rest ih =>
    cases candidate with
    | here =>
      cases opcode with
      | literal => simp [operands?, operandsFor?] at operands
      | add | mul =>
        cases edges with
        | cons lhs tail =>
          cases tail with
          | cons rhs empty =>
            cases empty
            simp [operands?, operandsFor?] at operands
      | sub =>
        cases edges with
        | cons lhs tail =>
          cases tail with
          | cons rhs empty =>
            cases empty
            simp [operands?, operandsFor?] at operands
            obtain ⟨rfl, rfl⟩ := operands
            apply congrArg (fun value : BitVec 64 =>
              rest.eval model entry (locals.snoc (.cons value .nil)))
            exact (BitVec.sub_self _).symm
    | later ref =>
      exact ih ref wire operands
        (locals.snoc (.cons (model.run opcode (edges.read entry locals)) .nil))

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program rewritten : Program SubZero.Opcode inputs out}
variable {candidate : Producer program.dataflow word}

private theorem admitted (accepted : fold? program candidate = some rewritten) :
    ∃ wire, operands? candidate = some (wire, wire) ∧
      { program with dataflow := replaceWithZero candidate } = rewritten := by
  cases operands : operands? candidate with
  | none => simp [fold?, operands] at accepted
  | some pair =>
    obtain ⟨lhs, rhs⟩ := pair
    simp only [fold?, operands, Option.bind_some] at accepted
    split at accepted
    · rename_i address
      obtain rfl := same_origin lhs rhs address
      exact ⟨lhs, rfl, Option.some.inj accepted⟩
    · cases accepted

theorem exact_source (accepted : fold? program candidate = some rewritten) :
    ∃ wire, operands? candidate = some (wire, wire) := by
  obtain ⟨wire, same, _⟩ := admitted accepted
  exact ⟨wire, same⟩

theorem sigs_eq (accepted : fold? program candidate = some rewritten) :
    rewritten.sigs = program.sigs := by
  obtain ⟨_, _, rfl⟩ := admitted accepted
  rfl

theorem locals_agree (accepted : fold? program candidate = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    HEq (rewritten.dataflow.eval model entry PUnit.unit) (program.dataflow.eval model entry PUnit.unit) := by
  obtain ⟨wire, same, rfl⟩ := admitted accepted
  exact heq_of_eq (replace_eval candidate wire same entry PUnit.unit)

theorem eval_eq (accepted : fold? program candidate = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry := by
  obtain ⟨wire, same, rfl⟩ := admitted accepted
  exact congrArg (Diamond.read model program.result entry) (replace_eval candidate wire same entry PUnit.unit)

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubSelf
