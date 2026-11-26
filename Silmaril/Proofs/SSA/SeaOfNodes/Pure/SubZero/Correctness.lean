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

private theorem read_zero (zero : Producer flow word) (checked : isZero zero = true)
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    Diamond.read model zero.origin entry (flow.eval model entry locals) = (0 : BitVec 64) := by
  have read := zero.read_key model entry locals
  cases key : zero.key with
  | mk ins opcode operands =>
    cases opcode with
    | literal value =>
      have same : value = 0 := by simpa [isZero, key] using checked
      cases operands
      rw [key] at read
      exact read.trans same
    | sub => simp [isZero, key] at checked

private theorem read_sub {sort : ValueSort Unit} (candidate : Producer flow sort)
    {lhs rhs : Origin args (operandScope candidate) wordPort}
    (found : operands? candidate = some (lhs, rhs))
    (entry : Tuple (Val model.value) args) (locals : Locals (Val model.value) past) :
    let final := flow.eval model entry locals
    HEq (Diamond.read model candidate.origin entry final)
      (BitVec.sub (Diamond.read model (inFinal candidate lhs) entry final)
        (Diamond.read model (inFinal candidate rhs) entry final)) := by
  induction candidate with
  | @here scope sigs ins out opcode edges rest =>
    cases opcode with
    | literal => simp [operands?] at found
    | sub =>
      cases edges with
      | cons left tail =>
        cases tail with
        | cons right empty =>
          cases empty
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
          exact heq_of_eq ((Producer.here (op := Opcode.sub) (inputs := .cons left (.cons right .nil))
            (rest := rest)).read_key model entry locals)
  | @later scope sigs ins out t opcode edges rest next ih =>
    exact ih found (locals.snoc (.cons (model.run opcode (edges.read entry locals)) .nil))

private theorem wire_eq {t : Ty Unit} (lhs rhs : Origin args past t) (same : lhs.address = rhs.address) :
    lhs = rhs :=
  congrArg (fun (wires : Wires args past [t]) => wires.get .head)
    (Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective (.cons lhs .nil) (.cons rhs .nil)
      (congrArg (fun address => [address]) same))

variable {inputs : List (ValueSort Unit)} {out : ValueSort Unit}
variable {program rewritten : Program Opcode inputs out}
variable {candidate zero : Producer program.dataflow word}

private theorem admitted (accepted : rewrite? program candidate zero = some rewritten) :
    ∃ lhs rhs, operands? candidate = some (lhs, rhs) ∧ isZero zero = true ∧
      inFinal candidate rhs = zero.origin ∧
      (let result := erase candidate lhs
       ({ dataflow := result.flow, result := result.route program.result } : Program Opcode inputs out)) =
        rewritten := by
  cases found : operands? candidate with
  | none => simp [rewrite?, found] at accepted
  | some pair =>
    obtain ⟨lhs, rhs⟩ := pair
    simp only [rewrite?, found, Option.bind_some] at accepted
    split at accepted
    · rename_i checked
      obtain ⟨literal, address⟩ := Bool.and_eq_true_iff.mp checked
      exact ⟨lhs, rhs, rfl, literal, wire_eq _ _ (of_decide_eq_true address), Option.some.inj accepted⟩
    · cases accepted

theorem old_rhs (accepted : rewrite? program candidate zero = some rewritten) :
    ∃ lhs rhs, operands? candidate = some (lhs, rhs) ∧ isZero zero = true ∧
      inFinal candidate rhs = zero.origin := by
  obtain ⟨lhs, rhs, found, literal, same, _⟩ := admitted accepted
  exact ⟨lhs, rhs, found, literal, same⟩

theorem count (accepted : rewrite? program candidate zero = some rewritten) :
    rewritten.sigs.length + 1 = program.sigs.length := by
  obtain ⟨lhs, _, _, _, _, rfl⟩ := admitted accepted
  exact GVN.Elimination.erase_size candidate lhs

theorem eval (accepted : rewrite? program candidate zero = some rewritten)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    rewritten.eval model entry = program.eval model entry := by
  obtain ⟨lhs, rhs, wires, literal, same, rfl⟩ := admitted accepted
  let final := program.dataflow.eval model entry PUnit.unit
  have zeroRhs : Diamond.read model (inFinal candidate rhs) entry final = (0 : BitVec 64) := by
    rw [same]
    exact read_zero zero literal entry PUnit.unit
  have equal : Diamond.read model candidate.origin entry final =
      Diamond.read model (inFinal candidate lhs) entry final :=
    (eq_of_heq (read_sub candidate wires entry PUnit.unit)).trans
      ((congrArg (BitVec.sub (Diamond.read model (inFinal candidate lhs) entry final)) zeroRhs).trans
        (BitVec.sub_zero _))
  exact (GVN.Elimination.erase_agrees candidate lhs model entry PUnit.unit equal _ program.result).symm

end Silmaril.Proofs.SSA.SeaOfNodes.Pure.SubZero
