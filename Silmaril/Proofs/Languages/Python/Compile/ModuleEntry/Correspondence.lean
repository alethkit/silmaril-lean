module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry

theorem global_reference {scope : Source.Scope} {name : Source.Name}
    (reference : GlobalReference scope name) : globalReference? scope name = some reference := by
  obtain ⟨_, resolved, moduleName | declared⟩ := reference
  · subst moduleName
    simp [globalReference?, resolved]
  · subst declared
    simp [globalReference?, resolved]

theorem chain_iff (left : Core.Module.Value) (links : List (ScalarComparison × Core.Module.Value))
    (value : Bool) : ScalarComparison.chain left links = value ↔ ScalarComparison.EvaluatesChain left links value := by
  induction links generalizing left value with
  | nil =>
    constructor
    · intro result
      cases result
      exact .done left
    · intro result
      cases result
      rfl
  | cons link rest ih =>
    rcases link with ⟨operator, right⟩
    constructor
    · intro result
      cases passed : operator.test left right with
      | false =>
        simp [ScalarComparison.chain, passed] at result
        exact result ▸ .stop passed
      | true =>
        exact .next passed ((ih right value).mp (by simpa [ScalarComparison.chain, passed] using result))
    · intro result
      cases result with
      | stop failed => simp [ScalarComparison.chain, failed]
      | next passed tail => simpa [ScalarComparison.chain, passed] using (ih right value).mpr tail

theorem literalComparisonChain_iff (left : Source.Expr) (first second : Source.Comparison × Source.Expr)
    (rest : List (Source.Comparison × Source.Expr)) (result : Bool) :
    literalComparisonChain? left (first :: second :: rest) = some result ↔
      ∃ initial links, scalarLiteral? left = some initial ∧
        (first :: second :: rest).mapM literalComparisonLink? = some links ∧
        ScalarComparison.EvaluatesChain initial links result := by
  cases initial : scalarLiteral? left <;>
    cases links : (first :: second :: rest).mapM literalComparisonLink? <;>
    simp [literalComparisonChain?, initial, links, chain_iff]

theorem selectScalar_iff (operator : Source.BooleanOperator) (value : Core.Module.Value)
    (rest : List Core.Module.Value) (result : Core.Module.Value) :
    selectScalar operator value rest = result ↔ SelectsScalar operator value rest result := by
  induction rest generalizing value result with
  | nil =>
    constructor
    · intro same
      cases same
      exact .last value
    · intro selected
      cases selected
      rfl
  | cons next rest ih =>
    constructor
    · intro selected
      cases h : continuesSelection operator value with
      | false =>
        simp [selectScalar, h] at selected
        exact selected ▸ .stop h
      | true => exact .next h ((ih next result).mp (by simpa [selectScalar, h] using selected))
    · intro selected
      cases selected with
      | stop stopped => simp [selectScalar, stopped]
      | next continued tail => simpa [selectScalar, continued] using (ih next result).mpr tail

theorem literalBooleanOp_iff (operator : Source.BooleanOperator) (first second : Source.Expr)
    (rest : List Source.Expr) (result : Core.Module.Value) :
    literalBooleanOp? operator (first :: second :: rest) = some result ↔
      ∃ initial remaining, scalarLiteral? first = some initial ∧
        (second :: rest).mapM scalarLiteral? = some remaining ∧
        SelectsScalar operator initial remaining result := by
  cases initial : scalarLiteral? first <;>
    cases remaining : (second :: rest).mapM scalarLiteral? <;>
    simp [literalBooleanOp?, initial, remaining, selectScalar_iff]

private theorem scalarTuple_none {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) : scalarTuple? source = none := by
  cases translated <;> rfl

theorem operand_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : OperandTranslation scope source operand) :
    lowerOperand scope source = .ok ⟨operand, translated⟩ := by
  induction translated with
  | integer => simp [lowerOperand]
  | boolean => simp [lowerOperand]
  | negativeInteger => simp [lowerOperand]
  | literalSubscript selected =>
    rw [lowerOperand]
    split
    · rename_i value computed
      have equal := Option.some.inj (computed.symm.trans selected)
      subst value
      rfl
    · simp_all
  | read _ witness => simp [lowerOperand, global_reference witness]; rfl
  | add _ _ left right => simp [lowerOperand, left, right]; rfl
  | floorDiv _ _ left right => simp [lowerOperand, left, right]; rfl
  | @equal sourceLeft sourceRight _ _ first _ left right =>
    have notFolded : literalTupleComparison? sourceLeft .eq sourceRight = none := by
      simp [literalTupleComparison?, scalarTuple_none first]
    rw [lowerOperand]
    split
    · rename_i value folded
      cases folded.symm.trans notFolded
    · rw [left, right]
      rfl
  | literalTupleComparison checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      have equal := Option.some.inj (computed.symm.trans checked)
      subst value
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalComparisonChain checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalNegation checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalBooleanOp checked =>
    rw [lowerOperand]
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent
  | literalConditional guard _ _ yes no =>
    rw [lowerOperand]
    split
    · simp_all
    · rename_i decision chosen
      have equal := Option.some.inj (chosen.symm.trans guard)
      subst decision
      rw [yes, no]
      rfl

theorem test_complete {scope : Source.Scope} {source : Source.Expr} {operand : Operand scope}
    (translated : TestTranslation scope source operand) : lowerTest scope source = .ok ⟨operand, translated⟩ := by
  cases translated with
  | operand translated =>
    have absent : nonScalarLiteralTruth? source = none := by cases translated <;> rfl
    unfold lowerTest
    split
    · rename_i value checked
      cases checked.symm.trans absent
    · rw [operand_complete translated]
      rfl
  | literalTruth checked =>
    unfold lowerTest
    split
    · rename_i value computed
      cases computed.symm.trans checked
      rfl
    · rename_i absent
      cases checked.symm.trans absent

theorem statements_complete {scope : Source.Scope} {source : List Source.Stmt} {actions : List (Action scope)}
    (translated : Translation scope source actions) : lowerStatements scope source = .ok ⟨actions, translated⟩ := by
  induction translated with
  | done => simp [lowerStatements]
  | @assign statement name expression reference value rest next binding operand _ tail =>
    cases binding <;> (simp [lowerStatements, binding?, global_reference reference, operand_complete operand, tail]; rfl)
  | assertion operand _ tail => simp [lowerStatements, test_complete operand, tail]; rfl
  | globals _ tail => simp [lowerStatements, tail]
  | pass _ tail => simp [lowerStatements, tail]
  | literalIf arms guard _ _ _ yes no tail =>
    rw [lowerStatements, dite_eq_left arms]
    split
    · simp_all
    · rename_i decision chosen
      have equal := Option.some.inj (chosen.symm.trans guard)
      subst decision
      rw [yes, no, tail]
      rfl

theorem check_complete {source : Source.Module} {tree : Source.ScopeTree}
    {actions : List (Action tree.scope)} (analyzed : Source.analyze source = .ok tree)
    (moduleScope : tree.scope.context.kind = .module_) (translated : Translation tree.scope source.body actions) :
    check source = .ok ⟨tree, analyzed, moduleScope, actions, translated⟩ := by
  unfold check
  split
  · rename_i _ rejected
    rw [analyzed] at rejected
    contradiction
  · rename_i other accepted
    have same := Except.ok.inj (accepted.symm.trans analyzed)
    subst other
    simp [moduleScope, statements_complete translated]; rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry
