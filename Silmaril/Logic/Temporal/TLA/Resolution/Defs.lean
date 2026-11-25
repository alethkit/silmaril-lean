module

public import Silmaril.Logic.Temporal.TLA.Resolution.Names

/-!
# TLA+ name and arity resolution

Resolve a Surface module and its EXTENDS closure against an explicit registry.
Each resolved use points to the identity of its declaration. The original trees
remain available for later passes. See `docs/projects/tla-module-resolution.md`.
-/

namespace Silmaril.Logic.Temporal.TLA.Resolution

open Surface

private abbrev Scope := List Binding

private def lookup (scope : Scope) (name : Name) : Option Binding :=
  let canonical := name.canonical
  scope.find? fun binding => binding.name = canonical

public section

/-- Additional syntax may be bound for the separate level-checking pass. -/
inductive Profile where
  | core
  | levelSyntax
  deriving DecidableEq, Repr

structure CheckedModule where
  private mk ::
  name : Ident
  source : Option Surface.Module
  imports : List ModuleId
  /-- All bindings introduced in this module, including lexical bindings. -/
  bindings : List Binding
  references : List (Path × Reference)
  /-- Final module scope, including inherited bindings, local definitions and built-ins. -/
  scope : List Binding
  deriving Repr

def CheckedModule.bindingAt (mod : CheckedModule) (name : Name) : Option Binding :=
  lookup mod.scope name

def CheckedModule.referenceAt (mod : CheckedModule) (path : Path) : Option Reference :=
  mod.references.lookup path

def CheckedModule.exports (mod : CheckedModule) : List Binding :=
  mod.scope.reverse.filter fun binding => !binding.isLocal && binding.kind ≠ .builtin

theorem CheckedModule.mem_exports (mod : CheckedModule) (binding : Binding) :
    binding ∈ mod.exports ↔ binding ∈ mod.scope ∧ binding.isLocal = false ∧
      binding.kind ≠ .builtin := by
  simp [exports]

structure CheckedRegistry where
  private mk ::
  root : ModuleId
  modules : List (ModuleId × CheckedModule)
  deriving Repr

def CheckedRegistry.moduleAt (checked : CheckedRegistry) (id : ModuleId) : Option CheckedModule :=
  checked.modules.lookup id

end

private def levelSyntaxOperators : List Name :=
  [.symbol .prefix "ENABLED", .symbol .prefix "UNCHANGED", .symbol .prefix "[]",
   .symbol .prefix "<>"]

private def deferredOperators : List Name :=
  [.symbol .infix "\\cdot", .symbol .infix "~>", .symbol .infix "-+->"]

/-- Named built-ins recognized by the pinned SANY frontend. Structural syntax
such as IF, records and junction lists has its own Surface constructors. -/
private def builtins : Scope :=
  let bind (name : Name) (arity : Nat) : Binding :=
    ⟨.builtin name, name, .builtin, List.replicate arity .expression, false⟩
  (["TRUE", "FALSE", "BOOLEAN", "STRING"].map fun name => bind (.ident name) 0) ++
  (["\\lnot", "SUBSET", "UNION", "DOMAIN"].map fun name => bind (.symbol .prefix name) 1) ++
  (["=", "/=", "\\land", "\\lor", "\\equiv", "=>", "\\subseteq", "\\in", "\\notin",
    "\\", "\\intersect", "\\union", "\\times"].map fun name => bind (.symbol .infix name) 2) ++
  [bind (.symbol .postfix "'") 1] ++
  (levelSyntaxOperators ++ deferredOperators).map fun name =>
    bind name (match name with | .symbol .infix _ => 2 | _ => 1)

public def CheckedRegistry.findBinding (checked : CheckedRegistry) : BindingId → Option Binding
  | .builtin name => builtins.find? fun binding => binding.name = name
  | .declared site => do
    let mod ← checked.moduleAt site.moduleId
    mod.bindings.find? fun binding => binding.id = .declared site

private structure ModuleState where
  bindings : List Binding := []
  references : List (Path × Reference) := []

private abbrev ModuleM := StateT ModuleState (Except Diagnostic)

private def diagnostic (site : Site) (kind : DiagnosticKind) : Diagnostic :=
  ⟨site, kind⟩

private def requireNonempty {α : Type} (site : Site) (form : String) (items : List α) : ModuleM Unit :=
  if items.isEmpty then throw (diagnostic site (.malformed form)) else pure ()

private def declare (scope : Scope) (site : Site) (name : Name) (kind : BindingKind)
    (slots : List Slot) (isLocal : Bool) : ModuleM Binding := do
  if let some previous := lookup scope name then
    throw (diagnostic site (.conflictingName name previous.id))
  let binding : Binding := ⟨.declared site, name.canonical, kind, slots, isLocal⟩
  modify fun state => { state with bindings := binding :: state.bindings }
  return binding

private def recordUse (profile : Profile) (scope : Scope) (site : Site) (name : Name)
    (role : ReferenceRole) : ModuleM Binding := do
  let some binding := lookup scope name
    | throw (diagnostic site (.unknownName name))
  if binding.name ∈ deferredOperators ||
      (profile = .core && binding.name ∈ levelSyntaxOperators) then
    throw (diagnostic site (.unsupported .actionOrTemporal))
  modify fun state =>
    { state with references := (site.path, ⟨binding.id, role⟩) :: state.references }
  return binding

private def visibilityIsLocal : Visibility → Bool
  | .ordinary => false
  | .local => true

private def declSignature : OperatorDecl → Name × Nat
  | .ident name arity => (.ident name, arity)
  | .symbolic (.prefix op) => (Name.ofSymbol (.prefix op), 1)
  | .symbolic (.infix op) => (Name.ofSymbol (.infix op), 2)
  | .symbolic (.postfix op) => (Name.ofSymbol (.postfix op), 1)

private def headSignature : OperatorHead → Name × List OperatorDecl
  | .ident name params => (.ident name, params)
  | .prefix op arg => (Name.ofSymbol (.prefix op), [.ident arg 0])
  | .infix left op right => (Name.ofSymbol (.infix op), [.ident left 0, .ident right 0])
  | .postfix arg op => (Name.ofSymbol (.postfix op), [.ident arg 0])

private def formalSlot (param : OperatorDecl) : Slot :=
  match (declSignature param).2 with
  | 0 => .expression
  | n + 1 => .operator (n + 1)

private def bindFormals (scope : Scope) (site : Site) (params : List OperatorDecl) :
    ModuleM Scope :=
  params.zipIdx.foldlM (init := scope) fun current (param, index) => do
    let (name, arity) := declSignature param
    let binding ← declare current (site.child (.parameter index)) name .formal
      (List.replicate arity .expression) true
    return binding :: current

private def bindNames (scope : Scope) (site : Site) (names : List Ident) : ModuleM Scope := do
  requireNonempty site "empty binder group" names
  names.zipIdx.foldlM (init := scope) fun current (name, index) => do
    let binding ← declare current (site.child (.binder index)) (.ident name) .rigid [] true
    return binding :: current

private def groupNames : BoundNames → List Ident
  | .names names | .tuple names => names

private def patternNames : BoundPattern → List Ident
  | .ident name => [name]
  | .tuple names => names

private def resolveBounds (visit : Site → Expr → ModuleM Unit) (scope : Scope)
    (site : Site) (groups : List Bound) : ModuleM Scope := do
  requireNonempty site "empty bounded group list" groups
  for (group, index) in groups.zipIdx do
    visit ((site.child (.bound index)).child .domain) group.domain
  groups.zipIdx.foldlM (init := scope) fun current (group, index) =>
    bindNames current (site.child (.bound index)) (groupNames group.names)

private def resolveDefinitionWith (visit : Scope → Site → Expr → ModuleM Unit)
    (scope : Scope) (site : Site) (definition : Definition) (inLet : Bool) : ModuleM Scope := do
  match definition with
  | .operator vis head body =>
    let (name, params) := headSignature head
    let binding ← declare scope site name .operator (params.map formalSlot)
      (inLet || visibilityIsLocal vis)
    -- Reserve the name for freshness checks, then keep it out of its own body.
    let withFormals ← bindFormals (binding :: scope) site params
    visit (withFormals.filter fun formal => formal.id ≠ binding.id) (site.child .body) body
    return binding :: scope
  | .function .. => throw (diagnostic site (.unsupported .functionDefinition))
  | .namedInstance .. => throw (diagnostic site (.unsupported .instantiation))

private def resolveOperatorArg (profile : Profile) (visit : Scope → Site → Expr → ModuleM Unit)
    (scope : Scope) (site : Site) (expected : Nat) (arg : OpArg) : ModuleM Unit := do
  let requireSignature (slots : List Slot) : ModuleM Unit :=
    unless slots = List.replicate expected .expression do
      throw (diagnostic site (.operatorArgumentMismatch expected slots))
  let named (name : Name) : ModuleM Unit := do
    let binding ← recordUse profile scope site name .operatorArgument
    requireSignature binding.slots
  match arg with
  | .symbolic op => named (Name.ofSymbol op)
  | .lambda params body =>
    requireNonempty site "empty lambda parameter list" params
    requireSignature (List.replicate params.length .expression)
    let inner ← bindFormals scope site (params.map fun name => .ident name 0)
    visit inner (site.child .body) body
  | .expr (.ref (.operator name) [] []) => named (Name.ofOperator name)
  | .expr (.ref (.step _) _ _) => throw (diagnostic site (.unsupported .proofReference))
  | .expr (.ref _ _ (_ :: _)) => throw (diagnostic site (.unsupported .qualifiedReference))
  | .expr _ => throw (diagnostic site (.expectedOperatorArgument expected))

private def resolveApplication (profile : Profile) (visit : Scope → Site → Expr → ModuleM Unit)
    (scope : Scope) (site : Site) (name : Name) (args : List OpArg)
    (child : Nat → Step) : ModuleM Unit := do
  let binding ← recordUse profile scope site name .application
  unless args.length = binding.slots.length do
    throw (diagnostic site (.arityMismatch name binding.slots.length args.length))
  for ((slot, arg), index) in (binding.slots.zip args).zipIdx do
    let argSite := site.child (child index)
    match slot, arg with
    | .expression, .expr body => visit scope argSite body
    | .expression, _ => throw (diagnostic argSite .expectedExpression)
    | .operator expected, arg => resolveOperatorArg profile visit scope argSite expected arg

private instance : Inhabited (ModuleM Unit) := ⟨pure ()⟩

-- Every recursive visit descends into a child of the current Surface expression.
private partial def resolveExpr (profile : Profile) (scope : Scope) (site : Site) (expr : Expr) :
    ModuleM Unit := do
  let visit := resolveExpr profile scope
  let operands (items : List Expr) : ModuleM Unit :=
    items.zipIdx.forM fun (item, index) => visit (site.child (.operand index)) item
  let apply (op : Symbol) (args : List Expr) :=
    resolveApplication profile (resolveExpr profile) scope site (Name.ofSymbol op)
      (args.map .expr) .operand
  match expr with
  | .ref (.step _) _ _ => throw (diagnostic site (.unsupported .proofReference))
  | .ref (.operator _) _ (_ :: _) => throw (diagnostic site (.unsupported .qualifiedReference))
  | .ref (.operator name) args [] =>
    resolveApplication profile (resolveExpr profile) scope site (Name.ofOperator name) args .argument
  | .literal _ => pure ()
  | .prefix op arg => apply (.prefix op) [arg]
  | .infix op left right => apply (.infix op) [left, right]
  | .postfix op arg => apply (.postfix op) [arg]
  | .cartesian factors =>
    if factors.length < 2 then throw (diagnostic site (.malformed "Cartesian product arity"))
    operands factors
  | .junction _ items =>
    requireNonempty site "empty junction" items
    operands items
  | .ifThenElse condition yes no => operands [condition, yes, no]
  | .cases arms other =>
    requireNonempty site "empty CASE" arms
    for (arm, index) in arms.zipIdx do
      let armSite := site.child (.arm index)
      visit (armSite.child (.operand 0)) arm.condition
      visit (armSite.child (.operand 1)) arm.result
    other.forM (visit (site.child .other))
  | .letIn declarations body =>
    requireNonempty site "empty LET" declarations
    let inner ← declarations.zipIdx.foldlM (init := scope) fun current (decl, index) =>
      let declSite := site.child (.letDecl index)
      match decl with
      | .definition definition =>
        resolveDefinitionWith (resolveExpr profile) current declSite definition true
      | .recursive _ => throw (diagnostic declSite (.unsupported .recursive))
    resolveExpr profile inner (site.child .body) body
  | .rigidQuant _ binders body =>
    let inner ← match binders with
      | .unbounded names => bindNames scope site names
      | .bounded groups => resolveBounds visit scope site groups
    resolveExpr profile inner (site.child .body) body
  | .choose pattern domain predicate =>
    domain.forM (visit (site.child .domain))
    let inner ← bindNames scope site (patternNames pattern)
    resolveExpr profile inner (site.child .body) predicate
  | .setFilter pattern domain predicate =>
    visit (site.child .domain) domain
    let inner ← bindNames scope site (patternNames pattern)
    resolveExpr profile inner (site.child .body) predicate
  | .setMap body bounds | .function bounds body =>
    let inner ← resolveBounds visit scope site bounds
    resolveExpr profile inner (site.child .body) body
  | .setEnum items | .tuple items => operands items
  | .functionSet domain range => operands [domain, range]
  | .index fn args =>
    requireNonempty site "empty index argument list" args
    operands (fn :: args)
  | .record fields | .recordSet fields =>
    fields.zipIdx.forM fun (field, index) => visit (site.child (.field index)) field.value
  | .field record _ => operands [record]
  | .except .. | .oldValue => throw (diagnostic site (.unsupported .except))
  | .action _ body subscript =>
    if profile = .core then throw (diagnostic site (.unsupported .actionOrTemporal))
    operands [body, subscript]
  | .fairness .. | .temporalQuant .. =>
    throw (diagnostic site (.unsupported .actionOrTemporal))
  | .labeled .. => throw (diagnostic site (.unsupported .labeledExpression))

private def resolveUnit (profile : Profile) (scope : Scope) (site : Site) (unit : ModuleUnit) : ModuleM Scope := do
  match unit with
  | .variables names =>
    requireNonempty site "empty VARIABLE declaration" names
    names.zipIdx.foldlM (init := scope) fun current (name, index) => do
      let binding ← declare current (site.child (.member index)) (.ident name) .variable [] false
      return binding :: current
  | .constants declarations =>
    requireNonempty site "empty CONSTANT declaration" declarations
    declarations.zipIdx.foldlM (init := scope) fun current (decl, index) => do
      let (name, arity) := declSignature decl
      let binding ← declare current (site.child (.member index)) name .constant
        (List.replicate arity .expression) false
      return binding :: current
  | .definition definition => resolveDefinitionWith (resolveExpr profile) scope site definition false
  | .instantiation .. => throw (diagnostic site (.unsupported .instantiation))
  | .recursive _ => throw (diagnostic site (.unsupported .recursive))
  | .submodule _ => throw (diagnostic site (.unsupported .submodule))
  | .assumption .. => throw (diagnostic site (.unsupported .assumption))
  | .theoremDecl ⟨none, .expr statement, none⟩ =>
    if profile = .core then throw (diagnostic site (.unsupported .theoremDecl))
    resolveExpr profile scope (site.child .body) statement
    return scope
  | .theoremDecl _ => throw (diagnostic site (.unsupported .theoremDecl))
  | .directive _ => throw (diagnostic site (.unsupported .proofDirective))

private def mergeExports (scope : Scope) (site : Site) (exports : List Binding) :
    Except Diagnostic Scope :=
  exports.foldlM (init := scope) fun current binding =>
    match lookup current binding.name with
    | none => pure (binding :: current)
    | some previous =>
      if previous.id = binding.id then pure current
      else throw (diagnostic site (.conflictingImport binding.name previous.id binding.id))

private def resolveSignature (scope : Scope) (site : Site) (decl : SignatureDecl) : ModuleM Scope := do
  let (name, kind, slots) ← match decl with
    | .variable name => pure (.ident name, .variable, [])
    | .constant decl =>
      let (name, arity) := declSignature decl
      pure (name, .constant, List.replicate arity .expression)
    | .operator name slots =>
      if .operator 0 ∈ slots then
        throw (diagnostic site (.malformed "zero-arity operator slot"))
      if let .symbol fixity _ := name then
        let arity := match fixity with | .infix => 2 | _ => 1
        unless slots = List.replicate arity .expression do
          throw (diagnostic site (.malformed "symbolic signature"))
      pure (name, .operator, slots)
  let binding ← declare scope site name kind slots false
  return binding :: scope

private def ModuleInput.header : ModuleInput → Ident
  | .parsed source _ => source.name
  | .signature name _ _ => name

private def ModuleInput.importsToResolve : ModuleInput → List Ident × ImportMap
  | .parsed source imports => (source.extendsModules, imports)
  | .signature _ imports _ => (imports.map Prod.fst, imports)

private def checkModule (profile : Profile) (site : Site) (input : ModuleInput)
    (imported : List ModuleId) (scope : Scope) : Except Diagnostic CheckedModule := do
  let (source, resolver) := match input with
    | .parsed source _ =>
      (some source, source.units.zipIdx.foldlM (init := scope) fun current (unit, index) =>
        resolveUnit profile current (site.child (.unit index)) unit)
    | .signature _ _ decls =>
      (none, decls.zipIdx.foldlM (init := scope) fun current (decl, index) =>
        resolveSignature current (site.child (.member index)) decl)
  let (finalScope, state) ← resolver.run {}
  return ⟨input.header, source, imported, state.bindings.reverse, state.references.reverse, finalScope⟩

private abbrev RegistryM := StateT (List (ModuleId × CheckedModule)) (Except Diagnostic)

private def resolveModules (profile : Profile) (registry : Registry) (fuel : Nat) (openModules : List ModuleId)
    (incoming : Site) (id : ModuleId) : RegistryM CheckedModule := do
  if id ∈ openModules then
    let cycle := (openModules.dropWhile (· != id)) ++ [id]
    throw (diagnostic incoming (.importCycle cycle))
  if let some checked := (← get).lookup id then return checked
  let some input := registry.lookup id | throw (diagnostic incoming (.unknownModule id))
  match fuel with
  | 0 => throw (diagnostic incoming (.malformed "dependency traversal exhausted"))
  | remaining + 1 =>
    let site : Site := ⟨id, []⟩
    let (names, links) := input.importsToResolve
    let mut scope := builtins
    let mut imported := []
    for (name, index) in names.zipIdx do
      let importSite := site.child (.import_ index)
      let target ← match links.filter (fun entry => entry.1 = name) with
        | [(_, target)] => pure target
        | [] => throw (diagnostic importSite (.unresolvedImport name))
        | _ => throw (diagnostic importSite (.duplicateImportMapping name))
      let some dependency := registry.lookup target
        | throw (diagnostic importSite (.unknownModule target))
      unless dependency.header = name do
        throw (diagnostic importSite (.importNameMismatch name dependency.header target))
      let checked ← resolveModules profile registry remaining (openModules ++ [id]) importSite target
      scope ← mergeExports scope importSite checked.exports
      imported := target :: imported
    let checked ← checkModule profile site input imported.reverse scope
    modify ((id, checked) :: ·)
    return checked

/-- Check every unit of every reachable parsed module. Inherited names retain
their declaration identity. The caller supplies EXTENDS edges. The level syntax
profile binds additional forms for a separate check of their levels. -/
public def resolveWith (profile : Profile) (registry : Registry) (root : ModuleId) :
    Except Diagnostic CheckedRegistry := do
  let mut seen := []
  for (id, _) in registry do
    if id ∈ seen then throw (diagnostic ⟨id, []⟩ (.duplicateModuleId id))
    seen := id :: seen
  let (_, checked) ← (resolveModules profile registry (registry.length + 1) [] ⟨root, []⟩ root).run []
  return ⟨root, checked.reverse⟩

/-- Resolve the core name-and-arity profile. -/
public def resolve (registry : Registry) (root : ModuleId) : Except Diagnostic CheckedRegistry :=
  resolveWith .core registry root

end Silmaril.Logic.Temporal.TLA.Resolution
