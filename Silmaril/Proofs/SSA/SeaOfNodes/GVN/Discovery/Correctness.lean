module

public import Silmaril.SSA.SeaOfNodes.GVN.Discovery.Defs

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery

open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN
open Silmaril.SSA.SeaOfNodes.GVN.Discovery
open Diamond (Dataflow Signature Ty ValueSort)
open Silmaril.SSA.RVSDG (Origin extend)

universe u v

private theorem olderIndex_val {T : Type u} (head : List T) :
    (scope : List (List T)) → (i : Fin scope.length) → (olderIndex head scope i).val = i.val
  | [], i => i.elim0
  | first :: tail, i =>
    Fin.cases (motive := fun j => (olderIndex head (first :: tail) j).val = j.val)
      rfl (fun j => congrArg Nat.succ (olderIndex_val head tail j)) i

private theorem newestIndex_val {T : Type u} (head : List T) :
    (scope : List (List T)) → (newestIndex head scope).val = scope.length
  | [] => rfl
  | _ :: tail => congrArg Nat.succ (newestIndex_val head tail)

private theorem weaken_producer {T : Type u} {args head : List T} {scope : List (List T)}
    {t : T} (wire : Origin args scope t) : (weaken head wire).producer = wire.producer := by
  cases wire with
  | arg => rfl
  | output i _ => exact congrArg some (olderIndex_val head scope i)

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

private theorem keepOrigin_producer {t : Ty Data} (flow : Dataflow Op args past sigs)
    (wire : Origin args past t) : (keepOrigin flow wire).producer = wire.producer := by
  induction flow with
  | nil => rfl
  | cons _ _ _ ih => exact (ih (weaken _ wire)).trans (weaken_producer wire)

private theorem origin_producer (ref : Producer flow out) :
    ref.origin.producer = some (past.length + position ref) := by
  induction ref with
  | @here past sigs ins out op inputs rest =>
    exact (keepOrigin_producer rest (newest (past := past) .head)).trans
      (congrArg some (newestIndex_val [.value out] past))
  | @later past sigs ins head out op inputs rest ref ih =>
    change ref.origin.producer = some (past.length + (position ref).succ)
    simpa [List.length_append, Nat.add_assoc, Nat.add_comm 1] using ih

variable [DecidableEq (ValueSort Data)]

theorem mem_earlier_iff (candidate representative : Producer flow out) :
    representative ∈ earlier candidate ↔ position representative < position candidate := by
  induction candidate with
  | here => simp [earlier, position]
  | @later past sigs ins head out op inputs rest next ih =>
    cases representative with
    | here => simp [earlier, position]
    | later ref =>
      by_cases same : head = out
      · subst out
        simp [earlier, position, List.mem_map, ih]
      · simp [earlier, position, same, List.mem_map, ih]

variable [∀ ins out, DecidableEq (Op ins out)]

theorem find_sound (candidate representative : Producer flow out)
    (found : findRepresentative? candidate = some representative) :
    checkRepresentative candidate representative = true :=
  List.find?_some found

theorem find_none_iff (candidate : Producer flow out) :
    findRepresentative? candidate = none ↔
      ∀ representative : Producer flow out, checkRepresentative candidate representative = false := by
  rw [findRepresentative?, List.find?_eq_none]
  constructor
  · intro rejected representative
    cases accepted : checkRepresentative candidate representative with
    | false => rfl
    | true =>
      have comparison := accepted
      simp only [checkRepresentative, origin_producer, Bool.and_eq_true, decide_eq_true_eq] at comparison
      have searched := (mem_earlier_iff candidate representative).2
        (Nat.lt_of_add_lt_add_left comparison.1)
      exact (rejected representative searched accepted).elim
  · intro rejected representative _ accepted
    rw [rejected representative] at accepted
    exact Bool.noConfusion accepted

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Discovery
