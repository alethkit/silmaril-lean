module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs
public import Silmaril.Languages.Python.Core.Closure.Thms

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure.Call

open Silmaril.Languages.Python.Core.Closure Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {bindings : List (ParameterSlot layout × Value)}
  {before after : Environment layout}

theorem writes_sound (bound : writeArguments bindings before = .ok after) : Writes bindings before after := by
  induction bindings generalizing before after with
  | nil =>
    change Except.ok before = .ok after at bound
    cases bound
    exact .nil before
  | cons binding rest ih =>
    obtain ⟨slot, value⟩ := binding
    rw [writeArguments] at bound
    cases written : before.2.write before.1 slot.slot value with
    | error error => simp [written, Except.bind] at bound
    | ok middle =>
      rw [written] at bound
      exact .cons written (ih bound)

theorem writes_complete (bound : Writes bindings before after) : writeArguments bindings before = .ok after := by
  induction bound with
  | nil => rfl
  | cons step _ ih =>
    rw [writeArguments, step]
    exact ih

theorem bind_iff {parameters : Parameters layout} {arguments : List Value} :
    bindPositional parameters arguments before = .ok after ↔
      arguments.length = parameters.slots.length ∧ Writes (parameters.slots.zip arguments) before after := by
  by_cases arity : arguments.length = parameters.slots.length
  · simpa [bindPositional, arity] using
      (show writeArguments (parameters.slots.zip arguments) before = .ok after ↔
          Writes (parameters.slots.zip arguments) before after from ⟨writes_sound, writes_complete⟩)
  · simp [bindPositional, arity]

private theorem write_slots {slot : ParameterSlot layout} {value : Value}
    (write : before.2.write before.1 slot.slot value = .ok after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures := by
  cases slot with
  | «local» index =>
    change Except.ok (before.1,
      { before.2 with locals := fun i => if i = index then some value else before.2.locals i }) = .ok after at write
    cases write
    exact ⟨rfl, rfl⟩
  | owned index =>
    have same := (Frame.writeCell_spec
      (show before.2.writeCell before.1 (before.2.owned index) value = .ok after from write)).1
    exact ⟨congrArg Frame.owned same, congrArg Frame.captures same⟩

theorem writes_preserve_ids (bound : Writes bindings before after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures := by
  induction bound with
  | nil => exact ⟨rfl, rfl⟩
  | cons write _ tail =>
    have head := write_slots write
    exact ⟨tail.1.trans head.1, tail.2.trans head.2⟩

variable {Continuation : Layout → Type} {fn : Function} {parameters : Parameters fn.code.layout}
  {arguments : List Value} {heap : Heap} {caller : Saved Continuation} {stack : List (Saved Continuation)}
  {callee : Entered Continuation fn.code.layout}

theorem enter_spec (entered : enter fn parameters arguments heap caller stack = .ok callee) :
    bindPositional parameters arguments (fn.freshFrame heap) = .ok callee.environment ∧
      callee.stack = caller :: stack := by
  cases valid : firstDangling fn heap with
  | some identity => simp [enter, valid] at entered
  | none =>
    cases binding : bindPositional parameters arguments (fn.freshFrame heap) with
    | error error => simp [enter, valid, binding, Except.map] at entered
    | ok initialized =>
      simp only [enter, valid, binding, Except.map, Except.ok.injEq] at entered
      cases entered
      exact ⟨rfl, rfl⟩

theorem enter_captures_live (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (captured : identity ∈ fn.captures.toList) : identity.address < heap.next := by
  have valid : firstDangling fn heap = none := by
    cases check : firstDangling fn heap with
    | none => rfl
    | some identity => simp [enter, check] at entered
  change fn.captures.toList.find? (fun cell => decide (heap.next ≤ cell.address)) = none at valid
  by_contra notLive
  have outside : heap.next ≤ identity.address := by omega
  exact (List.find?_eq_none.mp valid identity captured) (by simpa using outside)

end Silmaril.Proofs.Languages.Python.Core.Closure.Call
