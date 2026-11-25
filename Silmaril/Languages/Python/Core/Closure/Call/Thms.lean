module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {before after : Environment layout}

theorem bind_iff {parameters : Parameters layout} {arguments : List Value} :
    bindPositional parameters arguments before = .ok after ↔
      arguments.length = parameters.slots.length ∧ Writes (parameters.slots.zip arguments) before after :=
  Proofs.Languages.Python.Core.Closure.Call.bind_iff

theorem bind_preserves_ids {parameters : Parameters layout} {arguments : List Value}
    (bound : bindPositional parameters arguments before = .ok after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures :=
  Proofs.Languages.Python.Core.Closure.Call.writes_preserve_ids (bind_iff.mp bound).2

theorem bind_arity_error (parameters : Parameters layout) (arguments : List Value)
    (before : Environment layout) (wrong : arguments.length ≠ parameters.slots.length) :
    bindPositional parameters arguments before =
      .error (.defined (.positionalArity parameters.slots.length arguments.length)) := by
  simp [bindPositional, wrong]

variable {Continuation : Layout → Type} {fn : Function} {parameters : Parameters fn.code.layout}
  {arguments : List Value} {heap : Heap} {caller : Saved Continuation} {stack : List (Saved Continuation)}
  {callee : Entered Continuation fn.code.layout}

theorem enter_spec (entered : enter fn parameters arguments heap caller stack = .ok callee) :
    bindPositional parameters arguments (fn.freshFrame heap) = .ok callee.environment ∧
      callee.stack = caller :: stack :=
  Proofs.Languages.Python.Core.Closure.Call.enter_spec entered

theorem enter_captures_live (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (captured : identity ∈ fn.captures.toList) : identity.address < heap.next :=
  Proofs.Languages.Python.Core.Closure.Call.enter_captures_live entered captured

theorem enter_capture (entered : enter fn parameters arguments heap caller stack = .ok callee)
    (index : Fin fn.code.layout.captures) : callee.environment.2.captures index = fn.captures.get index :=
  congrFun (bind_preserves_ids (enter_spec entered).1).2 index

/-- The entire caller frame and continuation are restored for a return or a
defined error. Both deliveries carry the residual heap supplied by the callee. -/
theorem finish_after_enter (entered : enter fn parameters arguments heap caller stack = .ok callee)
    (residual : Heap) (result : Result) :
    finish residual callee.stack result = ⟨residual, stack, .resume caller result⟩ := by
  rw [(enter_spec entered).2]
  rfl

end Silmaril.Languages.Python.Core.Closure.Call
