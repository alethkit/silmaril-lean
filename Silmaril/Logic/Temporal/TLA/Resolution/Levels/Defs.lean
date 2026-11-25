module

public import Silmaril.Logic.Temporal.TLA.Resolution.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Summaries

/-!
# Compositional TLA+ expression levels

Check already-resolved first-order expressions against explicit level rules.
The result classifies source syntax and carries call constraints. See
`docs/projects/tla-expression-levels.md`.
-/

namespace Silmaril.Logic.Temporal.TLA.Resolution.Levels

open Surface

public section

inductive Unsupported where
  | operatorParameter | operatorArgument | expression | declaration
  deriving DecidableEq, Repr

inductive DiagnosticKind where
  | unsupported (form : Unsupported)
  | missingExternalSignature (id : BindingId)
  | duplicateExternalSignature (id : BindingId)
  | unexpectedExternalSignature (id : BindingId)
  | signatureArity (id : BindingId) (expected actual : Nat)
  | missingReference
  | missingBinding (id : BindingId)
  | missingSummary (id : BindingId)
  | inconsistentArity (expected actual : Nat)
  | failedRequirement (requirement : Requirement)
  deriving DecidableEq, Repr

structure Diagnostic where
  /-- The site being checked. A failed call also reports the requirement's origin. -/
  site : Site
  kind : DiagnosticKind
  deriving DecidableEq, Repr

structure CheckedLevels where
  private mk ::
  expressions : List (Site × LevelTerm)
  operators : List (BindingId × OperatorSummary)
  deriving Repr

def CheckedLevels.expressionAt (checked : CheckedLevels) (site : Site) : Option LevelTerm :=
  checked.expressions.lookup site

def CheckedLevels.operatorAt (checked : CheckedLevels) (id : BindingId) : Option OperatorSummary :=
  checked.operators.lookup id

end

private def weighted (floor : Level) (arguments : List ArgumentLevel) : ExternalSignature :=
  ⟨floor, arguments⟩

private def propagating (arity : Nat) (ceiling : Level) : ExternalSignature :=
  weighted .constant (List.replicate arity ⟨ceiling, true⟩)

private def logicalNames : List String := ["\\land", "\\lor", "=>", "\\equiv"]

/-- Named built-in ceilings and weights for the supported level profile. The
checker also applies the syntax guard for temporal modalities and the mixed
action/temporal guard for binary logical connectives. -/
public def builtinSignature (name : Name) : Option ExternalSignature :=
  match name.canonical with
  | .ident "TRUE" | .ident "FALSE" | .ident "BOOLEAN" | .ident "STRING" =>
    some (propagating 0 .constant)
  | .symbol .postfix "'" => some (weighted .action [⟨.state, false⟩])
  | .symbol .prefix "\\lnot" => some (propagating 1 .temporal)
  | .symbol .prefix "SUBSET" | .symbol .prefix "UNION" | .symbol .prefix "DOMAIN" =>
    some (propagating 1 .action)
  | .symbol .prefix "ENABLED" => some (weighted .state [⟨.action, false⟩])
  | .symbol .prefix "UNCHANGED" => some (weighted .action [⟨.state, false⟩])
  | .symbol .prefix "[]" | .symbol .prefix "<>" => some (weighted .temporal [⟨.temporal, false⟩])
  | .symbol .infix spelling =>
    if spelling ∈ logicalNames then some (propagating 2 .temporal)
    else if spelling ∈ ["=", "/=", "\\subseteq", "\\in", "\\notin", "\\",
        "\\intersect", "\\union", "\\times"] then some (propagating 2 .action)
    else none
  | _ => none

private structure Analysis where
  term : LevelTerm := {}
  requirements : List Requirement := []

private structure CheckerState where
  expressions : List (Site × LevelTerm) := []
  operators : List (BindingId × OperatorSummary) := []

private abbrev CheckM := StateT CheckerState (Except Diagnostic)

private def failAt {α : Type} (site : Site) (kind : DiagnosticKind) : CheckM α :=
  throw ⟨site, kind⟩

private def retain (site : Site) (requirements : List Requirement) :
    CheckM (List Requirement) := do
  let mut pending := []
  for requirement in requirements do
    unless requirement.condition.holds (fun _ => .constant) do
      failAt site (.failedRequirement requirement)
    if requirement.condition.dependsOnFormals then
      pending := requirement :: pending
  return pending.reverse

private def addCondition (analysis : Analysis) (site : Site) (condition : Condition) :
    CheckM Analysis := do
  let pending ← retain site [⟨site, condition⟩]
  return { analysis with requirements := analysis.requirements ++ pending }

private def applySignature (site : Site) (signature : ExternalSignature)
    (operands : List (Site × Analysis)) : CheckM Analysis := do
  unless operands.length = signature.arguments.length do
    failAt site (.inconsistentArity signature.arguments.length operands.length)
  let mut result := LevelTerm.fixed signature.floor
  let mut requirements := operands.flatMap fun (_, operand) => operand.requirements
  for (argument, operandSite, operand) in signature.arguments.zip operands do
    let pending ← retain operandSite [⟨operandSite, .atMost operand.term argument.maximum⟩]
    requirements := requirements ++ pending
    if argument.contributes then
      result := result.join operand.term
  return ⟨result, requirements⟩

private def applySummary (site : Site) (summary : OperatorSummary) (operands : List Analysis) :
    CheckM Analysis := do
  let some (result, requirements) := summary.instantiate (operands.map Analysis.term)
    | failAt site (.inconsistentArity summary.parameters.length operands.length)
  let pending ← retain site requirements
  return ⟨result, operands.flatMap Analysis.requirements ++ pending⟩

private def isMatchingBracket (name : Name) : Expr → Bool
  | .action .square _ _ => name = .symbol .prefix "[]"
  | .action .angle _ _ => name = .symbol .prefix "<>"
  | _ => false

private def applyBuiltin (site : Site) (name : Name) (sourceArgs : List Expr)
    (operands : List (Site × Analysis)) : CheckM Analysis := do
  let some signature := builtinSignature name | failAt site (.unsupported .expression)
  let result ← applySignature site signature operands
  match name, sourceArgs, operands with
  | .symbol .prefix spelling, [source], [(argSite, operand)] =>
    if (spelling = "[]" || spelling = "<>") && !isMatchingBracket name source then
      addCondition result argSite (.nonAction operand.term)
    else return result
  | .symbol .infix spelling, _, _ =>
    if spelling ∈ logicalNames then
      addCondition result site (.noMixedActionTemporal (operands.map fun (_, arg) => arg.term))
    else return result
  | _, _, _ => return result

private structure Context where
  registry : CheckedRegistry
  sourceModule : CheckedModule

private def checkApplication (visit : Site → Expr → CheckM Analysis) (context : Context)
    (site : Site) (args : List OpArg) (child : Nat → Step) : CheckM Analysis := do
  let some use := context.sourceModule.referenceAt site.path | failAt site .missingReference
  let some binding := context.registry.findBinding use.target | failAt site (.missingBinding use.target)
  for (slot, index) in binding.slots.zipIdx do
    if let .operator _ := slot then
      failAt (site.child (child index)) (.unsupported .operatorArgument)
  let exprs ← args.zipIdx.mapM fun (arg, index) =>
    match arg with
    | .expr value => pure value
    | _ => failAt (site.child (child index)) (.unsupported .operatorArgument)
  let operands ← exprs.zipIdx.mapM fun (expr, index) => do
    let argSite := site.child (child index)
    return (argSite, ← visit argSite expr)
  match binding.id, binding.kind with
  | .builtin name, _ => applyBuiltin site name exprs operands
  | _, .formal => return ⟨.parameter binding.id, []⟩
  | _, .rigid => return ⟨.fixed .constant, []⟩
  | _, _ =>
    let some summary := (← get).operators.lookup binding.id
      | failAt site (.missingSummary binding.id)
    applySummary site summary (operands.map Prod.snd)

private def formalId (site : Site) (index : Nat) : BindingId :=
  .declared (site.child (.parameter index))

private def checkDefinition (visit : Site → Expr → CheckM Analysis) (site : Site)
    (definition : Definition) : CheckM OperatorSummary := do
  let .operator _ head body := definition | failAt site (.unsupported .declaration)
  let arity ← match head with
    | .ident _ params =>
      for (param, index) in params.zipIdx do
        match param with
        | .ident _ 0 => pure ()
        | _ => failAt (site.child (.parameter index)) (.unsupported .operatorParameter)
      pure params.length
    | .infix .. => pure 2
    | _ => pure 1
  let result ← visit (site.child .body) body
  let summary : OperatorSummary :=
    ⟨(List.range arity).map (formalId site), result.term, result.requirements⟩
  modify fun state => { state with operators := (.declared site, summary) :: state.operators }
  return summary

private def checkBounded (visit : Site → Expr → CheckM Analysis) (site : Site) (bounds : List Bound)
    (body : Expr) (bodyCeiling : Level) (temporalQuantifier : Bool := false) : CheckM Analysis := do
  let ranges ← bounds.zipIdx.mapM fun (bound, index) => do
    let domain := (site.child (.bound index)).child .domain
    return (domain, ← visit domain bound.domain)
  let bodySite := site.child .body
  let checkedBody ← visit bodySite body
  let mut result ← applySignature site
    (weighted .constant (⟨bodyCeiling, true⟩ :: List.replicate ranges.length ⟨.action, true⟩))
    ((bodySite, checkedBody) :: ranges)
  if temporalQuantifier then
    for (domain, range) in ranges do
      result ← addCondition result domain (.temporalQuantifierBound checkedBody.term range.term)
  return result

private instance : Inhabited (CheckM Analysis) :=
  ⟨failAt ⟨"", []⟩ (.unsupported .expression)⟩

-- The visitor follows the same child paths as name resolution.
private partial def checkExpr (context : Context) (site : Site) (expression : Expr) :
    CheckM Analysis := do
  let visit := checkExpr context
  let child (step : Step) (expr : Expr) : CheckM (Site × Analysis) := do
    let childSite := site.child step
    return (childSite, ← visit childSite expr)
  let operands (items : List Expr) : CheckM (List (Site × Analysis)) :=
    items.zipIdx.mapM fun (expr, index) => child (.operand index) expr
  let structural (items : List Expr) (ceiling : Level) : CheckM Analysis := do
    applySignature site (propagating items.length ceiling) (← operands items)
  let apply (items : List Expr) : CheckM Analysis :=
    checkApplication visit context site (items.map .expr) .operand
  let checked ← match expression with
    | .literal _ => pure ({} : Analysis)
    | .ref (.operator _) args [] => checkApplication visit context site args .argument
    | .prefix _ arg | .postfix _ arg => apply [arg]
    | .infix _ left right => apply [left, right]
    | .cartesian items | .setEnum items | .tuple items => structural items .action
    | .junction _ items => do
      let args ← operands items
      let result ← applySignature site (propagating items.length .temporal) args
      addCondition result site (.noMixedActionTemporal (args.map fun (_, arg) => arg.term))
    | .ifThenElse condition yes no => structural [condition, yes, no] .temporal
    | .cases arms other => do
      let pairs ← arms.zipIdx.mapM fun (arm, index) => do
        let armSite := site.child (.arm index)
        let condition := armSite.child (.operand 0)
        let result := armSite.child (.operand 1)
        return [(condition, ← visit condition arm.condition), (result, ← visit result arm.result)]
      let fallback ← other.toList.mapM (child .other)
      let args := pairs.flatten ++ fallback
      applySignature site (propagating args.length .temporal) args
    | .letIn declarations body => do
      let mut requirements := []
      for (decl, index) in declarations.zipIdx do
        let declSite := site.child (.letDecl index)
        let .definition definition := decl | failAt declSite (.unsupported .declaration)
        let summary ← checkDefinition visit declSite definition
        let defaults := summary.parameters.map fun id => (id, LevelTerm.fixed .constant)
        requirements := requirements ++
          (← retain declSite (summary.requirements.map (·.substitute defaults)))
      let result ← visit (site.child .body) body
      pure { result with requirements := requirements ++ result.requirements }
    | .rigidQuant _ (.unbounded _) body => visit (site.child .body) body
    | .rigidQuant _ (.bounded bounds) body =>
      checkBounded visit site bounds body .temporal true
    | .choose _ domain predicate => do
      let range ← domain.toList.mapM (child .domain)
      let args := range ++ [← child .body predicate]
      applySignature site (propagating args.length .action) args
    | .setFilter _ domain predicate => do
      let args := [← child .domain domain, ← child .body predicate]
      applySignature site (propagating args.length .action) args
    | .setMap body bounds => checkBounded visit site bounds body .action
    | .function bounds body => checkBounded visit site bounds body .temporal
    | .functionSet domain range => structural [domain, range] .action
    | .index fn args => structural (fn :: args) .action
    | .record fields | .recordSet fields => do
      let args ← fields.zipIdx.mapM fun (field, index) => child (.field index) field.value
      let ceiling := match expression with | .recordSet _ => Level.action | _ => .temporal
      applySignature site (propagating args.length ceiling) args
    | .field record _ => structural [record] .action
    | .action _ body subscript => do
      let args ← operands [body, subscript]
      applySignature site (weighted .action [⟨.action, false⟩, ⟨.state, false⟩]) args
    | _ => failAt site (.unsupported .expression)
  let result := { checked with requirements := checked.requirements.eraseDups }
  modify fun state => { state with expressions := (site, result.term) :: state.expressions }
  return result

private def summaryFromSignature (site : Site) (signature : ExternalSignature) : OperatorSummary :=
  let params := (List.range signature.arguments.length).map (formalId site)
  let pairs := params.zip signature.arguments
  let term := pairs.foldl (fun result (id, arg) =>
    if arg.contributes then result.join (.parameter id) else result) (.fixed signature.floor)
  let requirements := pairs.zipIdx.filterMap fun ((id, arg), index) =>
    if arg.maximum = .temporal then none
    else some ⟨site.child (.parameter index), .atMost (.parameter id) arg.maximum⟩
  ⟨params, term, requirements⟩

private def registerDeclaration (external : ExternalLevels) (hasSource : Bool) (binding : Binding) :
    CheckM Unit := do
  let .declared site := binding.id | return ()
  let signature ← match binding.kind with
    | .variable => pure (weighted .state [])
    | .constant => pure (propagating binding.slots.length .temporal)
    | .operator =>
      if hasSource then return ()
      for (slot, index) in binding.slots.zipIdx do
        if let .operator _ := slot then
          failAt (site.child (.parameter index)) (.unsupported .operatorParameter)
      let some found := external.lookup binding.id | failAt site (.missingExternalSignature binding.id)
      unless found.arguments.length = binding.slots.length do
        failAt site (.signatureArity binding.id binding.slots.length found.arguments.length)
      pure found
    | _ => return ()
  let summary := summaryFromSignature site signature
  modify fun state => { state with operators := (binding.id, summary) :: state.operators }

private def checkModule (registry : CheckedRegistry) (external : ExternalLevels) (id : ModuleId)
    (resolved : CheckedModule) : CheckM Unit := do
  for binding in resolved.bindings do
    registerDeclaration external resolved.source.isSome binding
  let some source := resolved.source | return ()
  let context : Context := ⟨registry, resolved⟩
  let moduleSite : Site := ⟨id, []⟩
  for (unit, index) in source.units.zipIdx do
    let site := moduleSite.child (.unit index)
    match unit with
    | .definition definition => discard <| checkDefinition (checkExpr context) site definition
    | .variables _ | .constants _ => pure ()
    | .theoremDecl ⟨none, .expr statement, none⟩ =>
      discard <| checkExpr context (site.child .body) statement
    | _ => failAt site (.unsupported .declaration)

private def validateExternal (registry : CheckedRegistry) (external : ExternalLevels) : CheckM Unit := do
  let mut seen : List BindingId := []
  for (id, _) in external do
    let BindingId.declared site := id
      | failAt ⟨registry.root, []⟩ (.unexpectedExternalSignature id)
    if id ∈ seen then failAt site (.duplicateExternalSignature id)
    let some mod := registry.moduleAt site.moduleId | failAt site (.unexpectedExternalSignature id)
    let some binding := registry.findBinding id | failAt site (.unexpectedExternalSignature id)
    unless mod.source.isNone && binding.kind = .operator do
      failAt site (.unexpectedExternalSignature id)
    seen := id :: seen

/-- Check every reachable module and every body in its resolved syntax profile.
Signature-only operator declarations must have a supplied level signature. -/
public def check (registry : CheckedRegistry) (external : ExternalLevels := []) :
    Except Diagnostic CheckedLevels := do
  let verify : CheckM Unit := do
    validateExternal registry external
    for (id, mod) in registry.modules do
      checkModule registry external id mod
  let (_, state) ← verify.run {}
  return ⟨state.expressions.reverse, state.operators.reverse⟩

end Silmaril.Logic.Temporal.TLA.Resolution.Levels
