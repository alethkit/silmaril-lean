module

public import Silmaril.Languages.Python.Compile.Closure.VarNames.Defs

public section
namespace Silmaril.Languages.Python.Compile.Closure.VarNames

theorem Evidence.tuple_linked_parameters {tree : Source.ScopeTree}
    {blocks : List Link.Block} {ref : Core.Closure.CodeRef} (evidence : Evidence tree blocks ref) :
    let declared := linkedParameterNames evidence.block evidence.scope evidence.scopeLayout
    evidence.tuple =
      declared ++ (evidence.emittedNames.filter fun name => !declared.contains name).eraseDups := by
  rw [evidence.parameterOrder]
  rfl

theorem Evidence.tuple_single_parameter {tree : Source.ScopeTree}
    {blocks : List Link.Block} {ref : Core.Closure.CodeRef} (evidence : Evidence tree blocks ref)
    {name : Source.Name} (declared : evidence.scope.context.parameters = [name]) :
    evidence.tuple = name :: (evidence.emittedNames.filter fun other => !decide (other = name)).eraseDups := by
  simp [Evidence.tuple, declared]

theorem Evidence.tuple_without_emitted_names {tree : Source.ScopeTree}
    {blocks : List Link.Block} {ref : Core.Closure.CodeRef} (evidence : Evidence tree blocks ref)
    (unread : evidence.emittedNames = []) : evidence.tuple = evidence.scope.context.parameters := by
  simp [Evidence.tuple, unread]

end Silmaril.Languages.Python.Compile.Closure.VarNames
