module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Thms

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions

theorem Positional.length {scope : Source.Scope} {sources targets}
    (translated : Positional scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (Positional.length tail)

theorem CallArguments.length {scope : Source.Scope} {sources targets}
    (translated : CallArguments scope sources targets) : targets.length = sources.length :=
  match translated with
  | .nil => rfl
  | .cons _ tail => congrArg Nat.succ (CallArguments.length tail)

theorem global_read_resolved {scope : Source.Scope} {name : Source.Name}
    (global : Compile.Closure.Body.GlobalRead scope name) :
    scope.access name = some .implicitGlobal ∨ scope.access name = some .declaredGlobal :=
  match global with
  | .implicit access => Or.inl access
  | .declared access => Or.inr access

/-- A checked literal branch contributes the selected actions in order at
the current lexical child index, ahead of the rest of the module. -/
theorem lowerPlan_literalIf {tree : Source.ScopeTree} {index : Nat}
    {guard : Source.Expr} {yes no rest : List Source.Stmt}
    {selected : List (ModuleEntry.Action tree.scope)} {tail : List (Action tree.scope)}
    {tailTranslation : Translation tree index rest tail}
    (checked : ModuleEntry.Translation tree.scope [.if_ guard yes no] selected)
    (remaining : lowerPlan tree index rest = .ok ⟨tail, tailTranslation⟩) :
    (lowerPlan tree index (.if_ guard yes no :: rest)).toOption.map Subtype.val =
      some (selected.map .scalar ++ tail) := by
  simp [lowerPlan, callSite?, binding?, ModuleEntry.statements_complete checked, remaining,
    Except.mapError, Except.toOption]
  rfl

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions
