module

public import Silmaril.SSA.SeaOfNodes.GVN.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Equality.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Diamond (Dataflow Model Signature Ty Val ValueSort dataPorts)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires extend)

universe u v w

private theorem get_older {T : Type u} {F : T → Type w} {head : List T} {t : T}
    (next : Tuple F head) :
    (scope : List (List T)) → (i : Fin scope.length) → (port : Port scope[i] t) →
      (locals : Locals F scope) →
      ((locals.snoc next).get (olderIndex head scope i)).get (olderPort head scope i port) =
        (locals.get i).get port
  | [], i => i.elim0
  | first :: tail, i =>
    Fin.cases
      (motive := fun j => ∀ (port : Port (first :: tail)[j] t) (locals : Locals F (first :: tail)),
        ((locals.snoc next).get (olderIndex head (first :: tail) j)).get
          (olderPort head (first :: tail) j port) = (locals.get j).get port)
      (fun _ _ => rfl) (fun j port locals => get_older next tail j port locals.2) i

private theorem get_newest {T : Type u} {F : T → Type w} {head : List T} {t : T}
    (next : Tuple F head) (port : Port head t) {scope : List (List T)} (locals : Locals F scope) :
    ((locals.snoc next).get (newestIndex head scope)).get (newestPort port scope) = next.get port := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact ih locals.2

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))} {out : ValueSort Data}
variable (m : Model.{u,v,w} Op) (entry : Tuple (Val m.value) args)

private theorem read_weaken {head : List (Ty Data)} {t : Ty Data} (wire : Origin args past t)
    (locals : Locals (Val m.value) past) (next : Tuple (Val m.value) head) :
    Diamond.read m (weaken head wire) entry (locals.snoc next) = Diamond.read m wire entry locals := by
  cases wire with
  | arg => rfl
  | output i port => exact get_older next past i port locals

private theorem read_keep {t : Ty Data} (flow : Dataflow Op args past sigs) (wire : Origin args past t)
    (locals : Locals (Val m.value) past) :
    Diamond.read m (keepOrigin flow wire) entry (flow.eval m entry locals) =
      Diamond.read m wire entry locals := by
  induction flow with
  | nil => rfl
  | cons op inputs rest ih =>
    exact (ih (weaken _ wire) _).trans (read_weaken m entry wire locals _)

private theorem read_kept_operands {head ports : List (Ty Data)}
    (rest : Dataflow Op args (past ++ [head]) sigs) (wires : Wires args past ports)
    (locals : Locals (Val m.value) past) (next : Tuple (Val m.value) head) :
    Wires.read (wires.map (fun _ wire => keepOrigin rest (weaken head wire)))
      entry (rest.eval m entry (locals.snoc next)) = wires.read entry locals := by
  induction wires with
  | nil => rfl
  | cons wire tail ih =>
    simp only [Tuple.map, Wires.read] at ih ⊢
    congr 1
    change Diamond.read m (keepOrigin rest (weaken head wire)) entry
      (rest.eval m entry (locals.snoc next)) = Diamond.read m wire entry locals
    rw [read_keep]
    exact read_weaken m entry _ _ _

private theorem read_producer_key {flow : Dataflow Op args past sigs} (ref : Producer flow out)
    (locals : Locals (Val m.value) past) :
    let final := flow.eval m entry locals
    Diamond.read m ref.origin entry final = m.run ref.key.opcode (ref.key.operands.read entry final) := by
  induction ref with
  | @here past sigs ins out op inputs rest =>
    let value := m.run op (inputs.read entry locals)
    let next : Tuple (Val m.value) [.value out] := .cons value .nil
    have readNew : Diamond.read m (newest (past := past) .head) entry (locals.snoc next) = value :=
      get_newest next .head locals
    have readFinal := read_keep m entry rest (newest (past := past) .head) (locals.snoc next)
    exact (readFinal.trans readNew).trans
      (congrArg (m.run op) (read_kept_operands m entry rest inputs locals next).symm)
  | later _ ih =>
    simp only [Producer.origin, Producer.key, Dataflow.eval]
    exact ih _

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]

private theorem key_matches_read (left right : Key Op args past out)
    (locals : Locals (Val m.value) past) (accepted : left.matches right = true) :
    m.run left.opcode (left.operands.read entry locals) =
      m.run right.opcode (right.operands.read entry locals) := by
  rcases left with ⟨leftIns, leftOp, leftInputs⟩
  rcases right with ⟨rightIns, rightOp, rightInputs⟩
  by_cases sameTypes : leftIns = rightIns
  · subst rightIns
    have same : leftOp = rightOp ∧ leftInputs.addresses = rightInputs.addresses := by
      simpa [Key.matches] using accepted
    rw [same.1, Silmaril.SSA.RVSDG.NestedTheta.Equality.addresses_injective _ _ same.2]
  · simp [Key.matches, sameTypes] at accepted

theorem checkRepresentative_sound {flow : Dataflow Op args past sigs}
    (candidate representative : Producer flow out) (locals : Locals (Val m.value) past)
    (accepted : checkRepresentative candidate representative = true) :
    Diamond.read m candidate.origin entry (flow.eval m entry locals) =
      Diamond.read m representative.origin entry (flow.eval m entry locals) := by
  have sameKey : candidate.key.matches representative.key = true := by
    cases candidateId : candidate.origin.producer <;> cases representativeId : representative.origin.producer <;>
      simp [checkRepresentative, candidateId, representativeId] at accepted
    exact accepted.2
  rw [read_producer_key m entry candidate locals, read_producer_key m entry representative locals]
  exact key_matches_read m entry _ _ _ sameKey

end Silmaril.Proofs.SSA.SeaOfNodes.GVN
