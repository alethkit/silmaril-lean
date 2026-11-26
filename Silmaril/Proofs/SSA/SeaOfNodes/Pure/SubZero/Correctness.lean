module

public import Silmaril.SSA.SeaOfNodes.Pure.SubZero.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Pure
open Silmaril.SSA.SeaOfNodes.Pure.SubZero
open Diamond (Dataflow Ty Val ValueSort dataPorts)
open GVN (Producer)
open GVN.Elimination (erase inFinal operandScope)
open Silmaril.SSA.RVSDG (Locals Origin Tuple Wires)

variable {args : List (Ty Unit)} {past sigs : List (List (Ty Unit))}
variable {flow : Dataflow Opcode args past sigs}

private theorem read_literal (literal : Producer flow word) {expected : BitVec 64}
    (checked : isLiteral expected literal = true)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    Diamond.read model literal.origin entry (flow.eval model entry locals) = expected := by
  have read := literal.read_key model entry locals
  cases key : literal.key with
  | mk ins opcode operands =>
    cases opcode with
    | literal value =>
      have same : value = expected := by simpa [isLiteral, key] using checked
      cases operands
      rw [key] at read
      exact read.trans same
    | sub | add | mul => simp [isLiteral, key] at checked

private theorem read_binary {sort : ValueSort Unit} (candidate : Producer flow sort) {opcode : BinaryOpcode}
    {lhs rhs : Origin args (operandScope candidate) wordPort}
    (found : operandsFor? opcode candidate = some (lhs, rhs))
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    let final := flow.eval model entry locals
    HEq (Diamond.read model candidate.origin entry final)
      (model.run opcode (.cons (Diamond.read model (inFinal candidate lhs) entry final)
        (.cons (Diamond.read model (inFinal candidate rhs) entry final) .nil))) := by
  induction candidate with
  | @here scope sigs ins out actual edges rest =>
    cases actual with
    | literal => simp [operandsFor?] at found
    | sub | add | mul =>
      cases edges with
      | cons left tail =>
        cases tail with
        | cons right empty =>
          cases empty
          cases opcode <;> simp [operandsFor?] at found
          obtain ⟨rfl, rfl⟩ := found
          let read (op : BinaryOpcode) :=
            heq_of_eq ((Producer.here (op := op) (inputs := .cons left (.cons right .nil))
              (rest := rest)).read_key model entry locals)
          first | exact read .sub | exact read .add | exact read .mul
  | @later scope sigs ins out t opcode edges rest next ih =>
    exact ih found (locals.snoc (.cons (model.run opcode (edges.read entry locals)) .nil))

private theorem run_right_identity (opcode : BinaryOpcode) (lhs : BitVec 64) :
    model.run opcode (.cons lhs (.cons (rightIdentity opcode) .nil)) = lhs := by
  cases opcode
  · exact BitVec.sub_zero lhs
  · exact BitVec.add_zero lhs
  · exact BitVec.mul_one lhs

private theorem wire_eq {t : Ty Unit} (lhs rhs : Origin args past t) (same : lhs.address = rhs.address) :
    lhs = rhs :=
  congrArg (fun (wires : Wires args past [t]) => wires.get .head)
    (Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective (.cons lhs .nil) (.cons rhs .nil)
      (congrArg (fun address => [address]) same))

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program rewritten : Program Opcode inputs out}
variable {candidate literal : Producer program.dataflow word} {opcode : BinaryOpcode}

private theorem admitted (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten) :
    ∃ lhs rhs, operandsFor? opcode candidate = some (lhs, rhs) ∧
      isLiteral (rightIdentity opcode) literal = true ∧ inFinal candidate rhs = literal.origin ∧
      (let result := erase candidate lhs
       ({ dataflow := result.flow, result := result.route program.result } : Program Opcode inputs out)) =
        rewritten := by
  cases found : operandsFor? opcode candidate with
  | none => simp [rewriteRightIdentity?, found] at accepted
  | some pair =>
    obtain ⟨lhs, rhs⟩ := pair
    simp only [rewriteRightIdentity?, found, Option.bind_some] at accepted
    split at accepted
    · rename_i checked
      obtain ⟨literal, address⟩ := Bool.and_eq_true_iff.mp checked
      exact ⟨lhs, rhs, rfl, literal, wire_eq _ _ (of_decide_eq_true address), Option.some.inj accepted⟩
    · cases accepted

theorem exact_rhs (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten) :
    ∃ lhs rhs, operandsFor? opcode candidate = some (lhs, rhs) ∧
      isLiteral (rightIdentity opcode) literal = true ∧ inFinal candidate rhs = literal.origin := by
  obtain ⟨lhs, rhs, found, literal, same, _⟩ := admitted accepted
  exact ⟨lhs, rhs, found, literal, same⟩

theorem count (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten) :
    rewritten.sigs.length + 1 = program.sigs.length := by
  obtain ⟨lhs, _, _, _, _, rfl⟩ := admitted accepted
  exact GVN.Elimination.erase_size candidate lhs

theorem eval (accepted : rewriteRightIdentity? opcode program candidate literal = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry := by
  obtain ⟨lhs, rhs, wires, checked, same, rfl⟩ := admitted accepted
  let final := program.dataflow.eval model entry PUnit.unit
  have rhsValue : Diamond.read model (inFinal candidate rhs) entry final = rightIdentity opcode := by
    rw [same]
    exact read_literal literal checked entry PUnit.unit
  have equal : Diamond.read model candidate.origin entry final =
      Diamond.read model (inFinal candidate lhs) entry final := by
    have reads := eq_of_heq (read_binary candidate wires entry PUnit.unit)
    change Diamond.read model candidate.origin entry final =
      model.run opcode (.cons (Diamond.read model (inFinal candidate lhs) entry final)
        (.cons (Diamond.read model (inFinal candidate rhs) entry final) .nil)) at reads
    rw [reads, rhsValue]
    exact run_right_identity opcode _
  exact (GVN.Elimination.erase_agrees candidate lhs model entry PUnit.unit equal _ program.result).symm

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero
