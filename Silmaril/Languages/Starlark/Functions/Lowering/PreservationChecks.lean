module

import Silmaril.Languages.Starlark.Functions.Lowering.Thms

namespace Silmaril.Languages.Starlark.Functions.Lowering

open Lists (State)

private def events : Binding := ⟨.global, "events"⟩
private def destination : Binding := ⟨.global, "out"⟩

private def input : State :=
  { heap := #[⟨.list [], false⟩]
    bindings := fun name => if name = events then some (.list 0) else some (.scalar (.int 7)) }

private def afterAppend : State :=
  { input with heap := #[⟨.list [.scalar (.int 1)], false⟩] }

private def mark (n : Int) : Lists.Expr := .append (.read (.bound events)) (.scalar (.int n))

private theorem global_visible (name : String) : ¬ Scratch 0 ⟨.global, name⟩ := by
  rintro ⟨index, _, equal⟩
  simp [temporary] at equal

private theorem mark_runs :
    Evaluates #[] [] input (.atom (mark 1)) (.ok (.scalar .none) afterAppend) := by
  apply Evaluates.atom
  · exact .append (.bound (global_visible "events")) (.scalar _)
  · have receiver : Lists.Eval input (.read (.bound events)) (.ok (.list 0) input) :=
      Lists.Eval.read (s := input) (ref := .bound events)
    exact Lists.Eval.append receiver Lists.Eval.scalar

private def lenMark : Expr := .callPos (.atom (.builtin .len)) [.atom (mark 1)]

private def nestedFailure : Expr := .callPos (.atom (.builtin .len)) [lenMark, .atom (mark 2)]

-- The direct source derivation evaluates the callee and then the mutating
-- operand. It reports the failed application with the append still in the heap.
private theorem lenMark_fails :
    Evaluates #[] [] input lenMark (.error (.builtinType .len (.scalar .none)) afterAppend) := by
  apply Evaluates.call
  · exact .cons (.atom (.builtin _) .builtin) (.cons mark_runs .empty)
  · exact .builtin rfl (.lenCollection (by intro text equal; cases equal) (.invalid (by intro h; cases h)))

private theorem nested_fails :
    Evaluates #[] [] input nestedFailure (.error (.builtinType .len (.scalar .none)) afterAppend) :=
  .callError (.tailError (.atom (.builtin _) .builtin) (.headError lenMark_fails))

example : ∃ final,
    denoteBody #[] [] (lower nestedFailure destination).code input =
      .error (.builtinType .len (.scalar .none)) final ∧
    final.heap = afterAppend.heap ∧ final.bindingValue destination = .ok (.scalar (.int 7)) := by
  obtain ⟨final, ran, related⟩ := lower_preserves nested_fails (by intro _; rfl)
    destination (global_visible "out")
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

private def skipCall : Expr := .logical .and (.atom (mark 1))
  (.callPos (.atom (.builtin .len)) [.atom (mark 2)])

-- The same failing call is skipped when reached as the right operand of and.
private theorem skip_runs :
    Evaluates #[] [] input skipCall (.ok (.scalar .none) afterAppend) :=
  .shortCircuit mark_runs rfl rfl

example : ∃ final, denoteBody #[] [] (lower skipCall destination 3).code input = .ok .next final ∧
    final.heap = afterAppend.heap ∧ final.bindingValue destination = .ok (.scalar .none) := by
  obtain ⟨final, ran, related⟩ := lower_preserves skip_runs (by intro _; rfl)
    destination (global_visible "out") 3
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

end Silmaril.Languages.Starlark.Functions.Lowering
