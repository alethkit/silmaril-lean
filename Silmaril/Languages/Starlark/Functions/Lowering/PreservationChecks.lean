module

import Silmaril.Languages.Starlark.Functions.Lowering.Thms
import Silmaril.Languages.Starlark.Functions.Lowering.Denotation.Thms

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

private theorem mark_safe (n : Int) : AtomSafe (mark n) :=
  .append (.bound (global_visible "events")) (.scalar _)

private theorem mark_eval (s : State) (n : Int)
    (receiver : s.read (.bound events) = .ok (.list 0) s) :
    Lists.Eval s (mark n) (Lists.appendAt 0 (.scalar (.int n)) s) :=
  .append (receiver ▸ Lists.Eval.read) .scalar

private theorem mark_runs :
    Evaluates #[] [] input (.atom (mark 1)) (.ok (.scalar .none) afterAppend) :=
  .atom (mark_safe 1) (mark_eval input 1 rfl)

private def lenMark (n : Int) : Expr := .callPos (.atom (.builtin .len)) [.atom (mark n)]

private def nestedFailure : Expr := .callPos (.atom (.builtin .len)) [lenMark 1, .atom (mark 2)]

-- The direct source derivation evaluates the callee and then the mutating
-- operand. It reports the failed application with the append still in the heap.
private theorem lenMark_fails {s t : State} {n : Int}
    (runs : Evaluates #[] [] s (.atom (mark n)) (.ok (.scalar .none) t)) :
    Evaluates #[] [] s (lenMark n) (.error (.builtinType .len (.scalar .none)) t) := by
  refine Evaluates.call (keywords := []) (star := none) (starStar := none)
    (t := t) (values := [.builtin .len, .scalar .none]) ?_ ?_
  · exact .cons (.atom (.builtin _) .builtin) (.cons runs .empty)
  · exact .expanded (.success rfl rfl)
      (.builtin rfl (.lenCollection (by intro text equal; cases equal) (.invalid (by intro h; cases h))))

private theorem nested_fails :
    Evaluates #[] [] input nestedFailure (.error (.builtinType .len (.scalar .none)) afterAppend) :=
  .callError (keywords := []) (star := none) (starStar := none)
    (.tailError (.atom (.builtin _) .builtin) (.headError (lenMark_fails mark_runs)))

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

private theorem skip_admitted : Admitted skipCall := by
  refine .logical (.atom (mark_safe 1)) (.call ?_)
  intro operand member
  simp [sourceOperands] at member
  rcases member with rfl | rfl
  · exact .atom (.builtin .len)
  · exact .atom (mark_safe 2)

example : Evaluates #[] [] input skipCall (denoteExpr #[] [] skipCall input) :=
  (evaluates_iff_denoteExpr #[] [] skip_admitted input _).mpr rfl

example : ∃ final, denoteBody #[] [] (lower skipCall destination 3).code input = .ok .next final ∧
    final.heap = afterAppend.heap ∧ final.bindingValue destination = .ok (.scalar .none) := by
  obtain ⟨final, ran, related⟩ := lower_preserves skip_runs (by intro _; rfl)
    destination (global_visible "out") 3
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

private def marked (base : State) (ns : List Int) (tail : List Lists.Cell := []) : State :=
  { base with heap := (⟨.list (ns.map fun n => .scalar (.int n)), false⟩ :: tail).toArray }

private def keywordFailure : Expr :=
  .call (.atom (.builtin .len)) [.atom (mark 1)] [("ignored", lenMark 2)]
    (some (.atom (mark 3))) (some (.atom (mark 4)))

private theorem keywordFailure_runs :
    Evaluates #[] [] input keywordFailure
      (.error (.builtinType .len (.scalar .none)) (marked input [1, 2])) := by
  have second : Evaluates #[] [] afterAppend (.atom (mark 2)) (.ok (.scalar .none) (marked input [1, 2])) :=
    .atom (mark_safe 2) (mark_eval afterAppend 2 rfl)
  exact .callError (.tailError (.atom (.builtin _) .builtin) (.tailError mark_runs
    (.headError (lenMark_fails second))))

example :
    denoteExpr #[] [] keywordFailure input =
      .error (.builtinType .len (.scalar .none)) (marked input [1, 2]) :=
  denoteExpr_eq_of_evaluates keywordFailure_runs

example : ∃ final,
    denoteBody #[] [] (lower keywordFailure destination).code input =
      .error (.builtinType .len (.scalar .none)) final ∧
    final.heap = (marked input [1, 2]).heap ∧
    final.bindingValue destination = .ok (.scalar (.int 7)) := by
  obtain ⟨final, ran, related⟩ := lower_preserves keywordFailure_runs (by intro _; rfl)
    destination (global_visible "out")
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

private def invalidExpansions : Expr :=
  .call (.atom (.builtin .len)) [.atom (mark 1)] [("ignored", .atom (mark 2))]
    (some (.atom (mark 3))) (some (.atom (mark 4)))

-- Both expansions are invalid. Every operand runs first, and the mapping error wins.
private theorem invalidExpansions_run :
    Evaluates #[] [] input invalidExpansions (.error .invalidStarStar (marked input [1, 2, 3, 4])) := by
  refine .call (t := marked input [1, 2, 3, 4])
    (values := [.builtin .len, .scalar .none, .scalar .none, .scalar .none, .scalar .none]) ?_ ?_
  · exact .cons (.atom (.builtin _) .builtin) (.cons mark_runs
      (.cons (.atom (mark_safe 2) (mark_eval afterAppend 2 rfl))
        (.cons (.atom (mark_safe 3) (mark_eval (marked input [1, 2]) 3 rfl))
          (.cons (.atom (mark_safe 4) (mark_eval (marked input [1, 2, 3]) 4 rfl)) .empty))))
  · exact .expansionError (.mappingError rfl)

example :
    denoteExpr #[] [] invalidExpansions input = .error .invalidStarStar (marked input [1, 2, 3, 4]) :=
  denoteExpr_eq_of_evaluates invalidExpansions_run

example : ∃ final,
    denoteBody #[] [] (lower invalidExpansions destination).code input = .error .invalidStarStar final ∧
    final.heap = (marked input [1, 2, 3, 4]).heap ∧
    final.bindingValue destination = .ok (.scalar (.int 7)) := by
  obtain ⟨final, ran, related⟩ := lower_preserves invalidExpansions_run (by intro _; rfl)
    destination (global_visible "out")
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

private def emptyMapping : Lists.Expr := .dict .noEntries
private def emptyMapCell : Lists.Cell := ⟨.dict [], false⟩

private def invalidIterable : Expr :=
  .call (.atom (.builtin .len)) [] [] (some (.atom (mark 1))) (some (.atom emptyMapping))

-- A successful mapping expansion exposes the iterable error, retaining the allocation.
private theorem invalidIterable_runs :
    Evaluates #[] [] input invalidIterable (.error .invalidStar (marked input [1] [emptyMapCell])) := by
  refine .call (t := marked input [1] [emptyMapCell])
    (values := [.builtin .len, .scalar .none, .dict 1]) ?_ ?_
  · exact .cons (.atom (.builtin _) .builtin) (.cons mark_runs
      (.cons (.atom (.dict .noEntries) (Lists.Eval.dict (Lists.Eval.noEntries (s := afterAppend)))) .empty))
  · exact .expansionError (.spreadError (keys := []) (next := marked input [1] [emptyMapCell]) rfl rfl)

example : ∃ final,
    denoteBody #[] [] (lower invalidIterable destination).code input = .error .invalidStar final ∧
    final.heap = (marked input [1] [emptyMapCell]).heap ∧
    final.bindingValue destination = .ok (.scalar (.int 7)) := by
  obtain ⟨final, ran, related⟩ := lower_preserves invalidIterable_runs (by intro _; rfl)
    destination (global_visible "out")
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "out")⟩

private def functionName : Binding := ⟨.global, "f"⟩
private def closureCell : Lists.Cell := ⟨.function ⟨0, [], []⟩, false⟩
private def functionInput : State :=
  (marked input [] [closureCell]).write functionName (.function 1)

private def program : Program :=
  #[⟨{ positional := [⟨⟨.local, "x"⟩, none⟩] }, [], [], .total (.ret (.scalar .none))⟩]

private def duplicateMapping : Lists.Expr :=
  .dict (.entry .noEntries (.string "x") (mark 2))

private def duplicateName : Expr :=
  .call (.atom (.read (.bound functionName))) [] [("x", .atom (mark 1))]
    none (some (.atom duplicateMapping))

private def duplicateFinal : State :=
  marked functionInput [1, 2] [closureCell, ⟨.dict [⟨.string "x", [.string "x"], .scalar .none⟩], false⟩]

-- Binding rejects the duplicate only after both effects and the dict allocation.
private theorem duplicateName_runs :
    Evaluates program [0] functionInput duplicateName (.error (.multipleArgumentValues "x") duplicateFinal) := by
  have readFunction :
      Lists.Eval functionInput (.read (.bound functionName)) (.ok (.function 1) functionInput) :=
    .read (s := functionInput) (ref := .bound functionName)
  have first := mark_eval functionInput 1 rfl
  have second := mark_eval (marked functionInput [1] [closureCell]) 2 rfl
  have mapping : Lists.Eval (marked functionInput [1] [closureCell]) duplicateMapping
      (.ok (.dict 2) duplicateFinal) := by
    exact .dict (.entry .noEntries .string second)
  refine .call (t := duplicateFinal) (values := [.function 1, .scalar .none, .dict 2]) ?_ ?_
  · exact .cons (.atom (.bound (global_visible "f")) readFunction)
      (.cons (.atom (mark_safe 1) first)
        (.cons (.atom (.dict (.entry .noEntries (.string _) (mark_safe 2))) mapping) .empty))
  · exact .expanded (.success (next := duplicateFinal) (final := duplicateFinal)
      (keys := [("x", .scalar .none)]) (values := []) rfl rfl) (.reject rfl)

example :
    denoteExpr program [0] duplicateName functionInput = .error (.multipleArgumentValues "x") duplicateFinal :=
  denoteExpr_eq_of_evaluates duplicateName_runs

example : ∃ final,
    denoteBody program [0] (lower duplicateName destination).code functionInput =
      .error (.multipleArgumentValues "x") final ∧
    final.heap = duplicateFinal.heap ∧ final.bindingValue events = .ok (.list 0) ∧
    final.bindingValue destination = .ok (.scalar (.int 7)) := by
  obtain ⟨final, ran, related⟩ := lower_preserves duplicateName_runs (by intro _; rfl)
    destination (global_visible "out")
  exact ⟨final, ran, related.heap.symm, StateMatch.bindingValue_eq related (global_visible "events"),
    StateMatch.bindingValue_eq related (global_visible "out")⟩

end Silmaril.Languages.Starlark.Functions.Lowering
