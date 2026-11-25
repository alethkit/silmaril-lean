module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
import Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Correspondence

public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry

theorem ScalarComparison.chain_iff (left : Core.Module.Value) (links : List (ScalarComparison × Core.Module.Value))
    (value : Bool) : ScalarComparison.chain left links = value ↔ ScalarComparison.EvaluatesChain left links value :=
  Proofs.Languages.Python.Compile.ModuleEntry.chain_iff left links value

theorem literalComparisonChain_iff (left : Source.Expr) (first second : Source.Comparison × Source.Expr)
    (rest : List (Source.Comparison × Source.Expr)) (result : Bool) :
    literalComparisonChain? left (first :: second :: rest) = some result ↔
      ∃ initial links, scalarLiteral? left = some initial ∧
        (first :: second :: rest).mapM literalComparisonLink? = some links ∧
        ScalarComparison.EvaluatesChain initial links result :=
  Proofs.Languages.Python.Compile.ModuleEntry.literalComparisonChain_iff left first second rest result

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference :=
  Proofs.Languages.Python.Compile.ModuleEntry.global_reference reference

theorem operand_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) :
    lowerOperand scope source = .ok ⟨operand, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.operand_complete translated

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.statements_complete translated

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ :=
  Proofs.Languages.Python.Compile.ModuleEntry.check_complete analyzed moduleScope translated

end Silmaril.Languages.Python.Compile.ModuleEntry
