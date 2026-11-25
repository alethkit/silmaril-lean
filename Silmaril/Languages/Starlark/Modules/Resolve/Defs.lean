module

public import Silmaril.Languages.Starlark.Modules.Defs
public import Silmaril.Languages.Starlark.Functions.Lowering.Resolve.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve

open Functions
open Functions.Lowering.Resolve (Context resolveTracked)
open Lists.Iteration (LoopTarget)

structure SourceParameter where
  name : String
  defaultExpr : Option Lowering.Resolve.SourceExpr := none

/-- The parser or AST producer has separated the parameter classes. -/
structure SourceSignature where
  positional : List SourceParameter := []
  keywordOnly : List SourceParameter := []
  varargs : Option String := none
  kwargs : Option String := none

/-- Additional clauses and the element expression of an admitted list comprehension. -/
inductive ListCompTail where
  | yield (value : Lowering.Resolve.SourceExpr)
  | filter (test : Lowering.Resolve.SourceExpr) (rest : ListCompTail)
  | forIn (target iterable : Lowering.Resolve.SourceExpr) (rest : ListCompTail)

structure ListComp where
  target : Lowering.Resolve.SourceExpr
  iterable : Lowering.Resolve.SourceExpr
  rest : ListCompTail

/-- Admitted function statements. -/
inductive Statement where
  | pass
  | assign (name : String) (value : Lowering.Resolve.SourceExpr)
  | assignTarget (target rhs : Lowering.Resolve.SourceExpr)
  | assignListComp (name : String) (comp : ListComp)
  | setIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | addIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | eval (value : Lowering.Resolve.SourceExpr)
  | ret (value : Option Lowering.Resolve.SourceExpr)
  | seq (first rest : Statement)
  | branch (test : Lowering.Resolve.SourceExpr) (yes no : Statement)
  | forIn (target : String) (iterable : Lowering.Resolve.SourceExpr) (body : Statement)
  | forInTarget (target iterable : Lowering.Resolve.SourceExpr) (body : Statement)
  | breakLoop
  | continueLoop
  | define (name : String) (signature : SourceSignature) (body : Statement)

/-- Admitted module commands, in execution order. -/
inductive Command where
  | assign (name : String) (value : Lowering.Resolve.SourceExpr)
  | assignTarget (target rhs : Lowering.Resolve.SourceExpr)
  | assignListComp (name : String) (comp : ListComp)
  | setIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | addIndex (receiver subscript rhs : Lowering.Resolve.SourceExpr)
  | eval (value : Lowering.Resolve.SourceExpr)
  | define (name : String) (signature : SourceSignature) (body : Statement)
  | load (label : String) (imports : List Modules.Import)

inductive Error where
  | expression (error : Functions.Lowering.Resolve.Error)
  | validation (error : Modules.Error)
  | emptyLoad (label : String)
  | unsupportedLoopTarget
  | unsupportedAssignmentTarget
  | unsupportedComprehensionTarget
  deriving DecidableEq, Repr

structure ResolvedModule where
  program : Program
  source : Modules.Source

def fileNames (commands : List Command) : List String :=
  commands.flatMap fun
    | .load _ imports => imports.map Modules.Import.localName
    | _ => []

/-- Tuple and list spellings share the same resolved sequence target.
The normalized input supplies valid identifier spellings. -/
private def resolveTarget (slot : String → Binding) (unsupported : Error) :
    Lowering.Resolve.SourceExpr → Except Error (LoopTarget × List String)
  | .scalar (.read name) => pure (.name (slot name), [name])
  | .list elements | .tuple elements => do
    let children ← elements.attach.mapM fun ⟨expr, member⟩ => do
      have := List.sizeOf_lt_of_mem member
      resolveTarget slot unsupported expr
    return (.sequence (children.map Prod.fst), children.flatMap Prod.snd)
  | _ => throw unsupported

/-- Collect the module's lexical scope, including every valid pattern leaf.
Command elaboration rejects invalid targets. -/
def globalNames (commands : List Command) : List String :=
  commands.flatMap fun
    | .assign name _ | .assignListComp name _ | .define name .. => [name]
    | .assignTarget target _ =>
      ((resolveTarget globalSlot .unsupportedAssignmentTarget target).toOption.map Prod.snd).getD []
    | .setIndex .. | .addIndex .. | .eval _ | .load .. => []

private def Statement.localNames : Statement → Except Error (List String)
  | .assign name _ | .assignListComp name _ | .define name .. => pure [name]
  | .assignTarget target _ => return (← resolveTarget fileSlot .unsupportedAssignmentTarget target).2
  | .seq first rest | .branch _ first rest => return (← first.localNames) ++ (← rest.localNames)
  | .forIn target _ body => return target :: (← body.localNames)
  | .forInTarget target _ body =>
    return (← resolveTarget fileSlot .unsupportedLoopTarget target).2 ++ (← body.localNames)
  | .pass | .setIndex .. | .addIndex .. | .eval _ | .ret _ | .breakLoop | .continueLoop => pure []

private abbrev Build := StateT Program (Except Error)

private def readExpr (context : Context) (expression : Lowering.Resolve.SourceExpr) :
    Build (Lowering.Expr × List Binding) :=
  monadLift ((resolveTracked context expression).mapError Error.expression)

private def listCompTarget :=
  resolveTarget fileSlot .unsupportedComprehensionTarget

private def ListCompTail.names : ListCompTail → Except Error (List String)
  | .yield _ => pure []
  | .filter _ rest => rest.names
  | .forIn target _ rest => return (← listCompTarget target).2 ++ (← rest.names)

private def compileListCompTail (context : Context) :
    ListCompTail → Build (Comprehensions.Tail × List Binding)
  | .yield value => do
    let (value, reads) ← readExpr context value
    return (.yield value, reads)
  | .filter test rest => do
    let (test, reads) ← readExpr context test
    let (rest, restReads) ← compileListCompTail context rest
    return (.filter test rest, reads ++ restReads)
  | .forIn target iterable rest => do
    let (target, _) ← monadLift (listCompTarget target)
    let (iterable, reads) ← readExpr context iterable
    let (rest, restReads) ← compileListCompTail context rest
    return (.forIn target iterable rest, reads ++ restReads)

private def compileListComp (context : Context) (comp : ListComp) :
    Build (Comprehensions.ListComp × List Binding) := do
  let (target, firstNames) ← monadLift (listCompTarget comp.target)
  let names := (firstNames ++ (← monadLift comp.rest.names)).eraseDups
  let locals := names.map fileSlot
  let (iterable, outerReads) ← readExpr context comp.iterable
  let (rest, innerReads) ← compileListCompTail { context with locals := names ++ context.locals } comp.rest
  return (⟨locals, target, iterable, rest⟩, outerReads ++ innerReads.filter (!locals.contains ·))

private def resolveSubscript (context : Context) (receiver subscript : Lowering.Resolve.SourceExpr) :
    Build (Lowering.Expr × Lowering.Expr × List Binding) := do
  let (receiver, receiverReads) ← readExpr context receiver
  let (subscript, subscriptReads) ← readExpr context subscript
  return (receiver, subscript, receiverReads ++ subscriptReads)

private def resolveSetIndex {α : Type} (context : Context)
    (receiver subscript rhs : Lowering.Resolve.SourceExpr)
    (emit : Lowering.Expr → Lowering.Expr → Lowering.Expr → α) : Build (α × List Binding) := do
  let (rhs, rhsReads) ← readExpr context rhs
  let (receiver, subscript, reads) ← resolveSubscript context receiver subscript
  return (emit receiver subscript rhs, rhsReads ++ reads)

private def resolveAddIndex {α : Type} (context : Context)
    (receiver subscript rhs : Lowering.Resolve.SourceExpr)
    (emit : Lowering.Expr → Lowering.Expr → Lowering.Expr → α) : Build (α × List Binding) := do
  let (receiver, subscript, reads) ← resolveSubscript context receiver subscript
  let (rhs, rhsReads) ← readExpr context rhs
  return (emit receiver subscript rhs, reads ++ rhsReads)

private def readParameter (context : Context) (parameter : SourceParameter) :
    Build (Functions.Parameter × List Binding) := do
  let slot := fileSlot parameter.name
  match parameter.defaultExpr with
  | none => return (⟨slot, none⟩, [])
  | some expression =>
    let (value, reads) ← readExpr context expression
    return (⟨slot, some value⟩, reads)

private structure ResolvedBody where
  code : Body
  reads : List Binding

private def captureNames (owned : List String) (reads : List Binding) : List FreeName :=
  (reads.eraseDups.filter fun binding => binding.scope == .global || !owned.contains binding.name).map
    fun binding => ⟨binding, binding⟩

private def compileDefinition (parent : Context) (parameters : SourceSignature) (locals : List String)
    (compile : Context → Build ResolvedBody) : Build (DeclarationId × List Binding) := do
  let positional ← parameters.positional.mapM (readParameter parent)
  let keywords ← parameters.keywordOnly.mapM (readParameter parent)
  let signature : Functions.Signature := ⟨positional.map Prod.fst, keywords.map Prod.fst,
    parameters.varargs.map fileSlot, parameters.kwargs.map fileSlot⟩
  let parameterNames := signature.slots.map Binding.name
  let locals := locals.eraseDups.filter (!parameterNames.contains ·)
  let owned := parameterNames ++ locals
  let body ← compile { parent with locals := owned ++ parent.locals }
  let captures := captureNames owned body.reads
  let program ← get
  set (program.push ⟨signature, locals.map fileSlot, captures, body.code⟩)
  -- A child needs its captures when it is defined. Its defaults also read the parent.
  return (program.size, (positional ++ keywords).flatMap Prod.snd ++ captures.map FreeName.source)

private def compileBody (context : Context) : Statement → Build ResolvedBody
  | .pass => pure ⟨.total (.atomic .pass), []⟩
  | .assign name value => do
    let (value, reads) ← readExpr context value
    return ⟨.assignExpr (fileSlot name) value, reads⟩
  | .assignTarget target rhs => do
    let (target, _) ← monadLift (resolveTarget fileSlot .unsupportedAssignmentTarget target)
    let (rhs, reads) ← readExpr context rhs
    return ⟨.assignTargetExpr target rhs, reads⟩
  | .assignListComp name comp => do
    let (comp, reads) ← compileListComp context comp
    return ⟨comp.body (fileSlot name), reads⟩
  | .setIndex receiver subscript rhs => do
    let (code, reads) ← resolveSetIndex context receiver subscript rhs Body.setIndexExpr
    return ⟨code, reads⟩
  | .addIndex receiver subscript rhs => do
    let (code, reads) ← resolveAddIndex context receiver subscript rhs Body.addIndexExpr
    return ⟨code, reads⟩
  | .eval value => do
    let (value, reads) ← readExpr context value
    return ⟨.evalExpr value, reads⟩
  | .ret none => pure ⟨.returnExpr (.atom (.scalar .none)), []⟩
  | .ret (some value) => do
    let (value, reads) ← readExpr context value
    return ⟨.returnExpr value, reads⟩
  | .seq first rest => do
    let first ← compileBody context first
    let rest ← compileBody context rest
    return ⟨.seq first.code rest.code, first.reads ++ rest.reads⟩
  | .branch test yes no => do
    let (test, reads) ← readExpr context test
    let yes ← compileBody context yes
    let no ← compileBody context no
    return ⟨.branchExpr test yes.code no.code, reads ++ yes.reads ++ no.reads⟩
  | .forIn target iterable body => do
    let (iterable, reads) ← readExpr context iterable
    let body ← compileBody context body
    return ⟨.forInExpr (fileSlot target) iterable body.code, reads ++ body.reads⟩
  | .forInTarget target iterable body => do
    let (target, _) ← monadLift (resolveTarget fileSlot .unsupportedLoopTarget target)
    let (iterable, reads) ← readExpr context iterable
    let body ← compileBody context body
    return ⟨.forInExpr target iterable body.code, reads ++ body.reads⟩
  | .breakLoop => pure ⟨.breakLoop, []⟩
  | .continueLoop => pure ⟨.continueLoop, []⟩
  | .define name signature body => do
    let locals ← monadLift body.localNames
    let (id, reads) ←
      compileDefinition context signature locals (fun inner => compileBody inner body)
    return ⟨.define (fileSlot name) id, reads⟩
termination_by structural statement => statement

private def compileCommand (context : Context) : Command → Build Modules.Command
  | .assign name value => do
    let (value, _) ← readExpr context value
    return .exec (.assignExpr name value)
  | .assignTarget target rhs => do
    let (target, _) ← monadLift (resolveTarget globalSlot .unsupportedAssignmentTarget target)
    let (rhs, _) ← readExpr context rhs
    return .exec (.assignTargetExpr target rhs)
  | .assignListComp name comp => do
    let (comp, _) ← compileListComp context comp
    return .exec (.assignListComp name comp)
  | .setIndex receiver subscript rhs => do
    let (code, _) ← resolveSetIndex context receiver subscript rhs TopCode.setIndexExpr
    return .exec code
  | .addIndex receiver subscript rhs => do
    let (code, _) ← resolveAddIndex context receiver subscript rhs TopCode.addIndexExpr
    return .exec code
  | .eval value => do
    let (value, _) ← readExpr context value
    return .exec (.evalExpr value)
  | .define name signature body => do
    let locals ← monadLift body.localNames
    let (id, _) ←
      compileDefinition context signature locals (fun inner => compileBody inner body)
    return .exec (.define name id)
  | .load label imports =>
    if imports.isEmpty then throw (.emptyLoad label) else pure (.load label imports)

/-- Elaborate in source order, appending declarations to the supplied linked
table. Call `resolve` for checked intake. -/
def elaborateCommands (commands : List Command) (linked : Program := #[]) :
    Except Error (List Modules.Command × Program) :=
  let context : Context := ⟨fileNames commands, globalNames commands⟩
  (commands.mapM (compileCommand context)) linked

/-- Elaborate and validate the emitted declaration table and commands.
Input names are normalized identifiers. -/
@[expose] def resolve (commands : List Command) (linked : Program := #[]) : Except Error ResolvedModule :=
  match elaborateCommands commands linked with
  | .error error => .error error
  | .ok (code, program) =>
    let source : Modules.Source := ⟨globalNames commands, [], code⟩
    match validateSource program source with
    | .error error => .error (.validation error)
    | .ok () => .ok ⟨program, source⟩

abbrev Result := Except Error (Modules.Result Published)

/-- Static rejection is separate from execution. Successful elaboration uses
the resolved module evaluator. When catalog values can contain closures,
supply their original heap and linked declarations. -/
@[expose] def runModule (commands : List Command) (host : Catalog) (caller : Lists.State)
    (linked : Program := #[]) : Result :=
  match resolve commands linked with
  | .error error => .error error
  | .ok resolved => .ok (initializeModule resolved.program host resolved.source caller)

end Silmaril.Languages.Starlark.Modules.Resolve
