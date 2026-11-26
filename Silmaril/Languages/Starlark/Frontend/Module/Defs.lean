module

public import Silmaril.Languages.Starlark.Frontend.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Defs

/-! # Source text to normalized Starlark modules

The adapter preserves command order and locations and uses the existing checked
module entry point for resolution, execution, and publication.
-/

public section

namespace Silmaril.Languages.Starlark.Frontend.Module

open Modules (Published)

structure LocatedCommand where
  span : Span
  command : Modules.Resolve.Command
  callSpans : Option CallSpans := none

structure ParsedModule where
  commands : List LocatedCommand

@[expose] def ParsedModule.toCommands (parsed : ParsedModule) : List Modules.Resolve.Command :=
  parsed.commands.map LocatedCommand.command

private def lowerExpr (span : Span) : SourceExpr →
    Except Diagnostic Functions.Lowering.Resolve.SourceExpr
  | .unary .. | .binary .. => .error ⟨.unsupported .operator, span⟩
  | .conditional test yes no =>
    return .conditional (← lowerExpr span test) (← lowerExpr span yes) (← lowerExpr span no)
  | .logical op left right => return .logical op (← lowerExpr span left) (← lowerExpr span right)
  | .int value => pure (.scalar (.int value))
  | .read name => pure (.scalar (.read name))

private def lowerStmt (span : Span) : SourceStmt → Except Diagnostic Modules.Resolve.Statement
  | .pass => pure .pass
  | .assign name rhs => return .assign name (← lowerExpr span rhs)
  | .eval value => return .eval (← lowerExpr span value)
  | .ret value => return .ret (← value.mapM (lowerExpr span))
  | .seq first rest => return .seq (← lowerStmt span first) (← lowerStmt span rest)
  | .branch test yes no =>
    return .branch (← lowerExpr span test) (← lowerStmt span yes) (← lowerStmt span no)

private def lowerParameter (parameter : LocatedParameter) :
    Except Diagnostic Modules.Resolve.SourceParameter := do
  let defaultExpr ← parameter.defaultValue.mapM fun value =>
    Modules.Resolve.CompExpr.plain <$> lowerExpr value.span value.expr
  return ⟨parameter.name, defaultExpr⟩

private def lowerFunction (fn : LocatedFunction) : Except Diagnostic Modules.Resolve.Command := do
  let positional ← fn.parameters.mapM lowerParameter
  let body ← fn.body.mapM fun stmt => lowerStmt stmt.span stmt.stmt
  let body := match body.reverse with
    | [] => .pass
    | last :: preceding => preceding.foldl (fun rest first => .seq first rest) last
  return .define fn.name { positional } body

private def lowerArgument (argument : LocatedArgument) :
    Except Diagnostic Functions.Lowering.Resolve.SourceExpr := lowerExpr argument.span argument.expr

/-- Lower a named group in order and retain every explicit name for validation. -/
def lowerNamedArguments (arguments : List LocatedNamedArgument) :
    Except Diagnostic (List (String × Functions.Lowering.Resolve.SourceExpr)) :=
  arguments.mapM fun argument => do
    return (argument.name, ← lowerArgument argument.value)

private def lowerDisplay : CollectionDisplay → Except Diagnostic Functions.Lowering.Resolve.SourceExpr
  | .sequence isTuple operands => do
    let elements ← operands.mapM lowerArgument
    return if isTuple then .tuple elements else .list elements
  | .mapping operands => do
    let entries ← operands.mapM fun entry => do
      return (Functions.Lowering.Resolve.SourceExpr.string entry.name, ← lowerArgument entry.value)
    return .dict entries

private def lowerSpread (spread : LocatedSpread) :
    Except Diagnostic Functions.Lowering.Resolve.SourceExpr :=
  match spread.operand with
  | .name name => pure (.scalar (.read name))
  | .display display => lowerDisplay display

structure LoweredCall where
  expression : Functions.Lowering.Resolve.SourceExpr
  spans : CallSpans

/-- Project the span groups onto the normalized binder's argument shape. -/
def callShape (spans : CallSpans) : Functions.ArgumentShape :=
  Functions.Lowering.argumentShape spans.positional spans.named spans.star spans.starStar

/-- Lower the groups in source order and retain their original operand spans. -/
def lowerCall (callee : String) (arguments : LocatedCallArguments) : Except Diagnostic LoweredCall := do
  let positional ← arguments.positional.mapM lowerArgument
  let named ← lowerNamedArguments arguments.named
  let star ← arguments.star.mapM lowerSpread
  let starStar ← arguments.starStar.mapM lowerSpread
  return ⟨.call (.scalar (.read callee)) positional named star starStar, arguments.spans⟩

private def lowerCommand (source : LocatedFileCommand) :
    Except Diagnostic (Option LocatedCommand) := do
  let located (command : Modules.Resolve.Command) : Option LocatedCommand :=
    some { span := source.span, command }
  match source.command with
  | .simple .pass => return none
  | .simple (.assign name rhs) => return located (.assign name (← lowerExpr source.span rhs))
  | .simple (.eval value) => return located (.eval (← lowerExpr source.span value))
  | .simple _ => .error ⟨.unsupported .compoundStatement, source.span⟩
  | .define fn => return located (← lowerFunction fn)
  | .assignDisplay target display => return located (.assign target (← lowerDisplay display))
  | .assignCall target callee arguments =>
    let call ← lowerCall callee arguments
    return some ⟨source.span, .assign target call.expression, some call.spans⟩
  | .load label imports =>
    return located (.load label.text (imports.map fun item => ⟨item.exported.text, item.localName.text⟩))

private def lowerCommands (source : List LocatedFileCommand) : Except Diagnostic ParsedModule := do
  return ⟨(← source.mapM lowerCommand).filterMap id⟩

/-- Parse a file and produce the normalized module commands with their source spans. -/
def parse (source : String) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFile source)

/-- Parse and normalize original UTF-8 file bytes. -/
def parseUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFileUtf8 source)

/-- Initialize a module with an empty import catalog. Use the finite loader for load graphs. -/
@[expose] def ParsedModule.run (parsed : ParsedModule) : Modules.Resolve.Result :=
  Modules.Resolve.runModule parsed.toCommands (fun _ => none) {}

inductive IntakeError where
  | frontend (diagnostic : Diagnostic)
  | validation (error : Modules.Resolve.Error)
  deriving DecidableEq, Repr

/-- Frontend and validation failures precede the runtime result. Runtime failure
carries the existing residual state and no publication. -/
def runUtf8 (source : ByteArray) : Except IntakeError (Modules.Result Published) := do
  let parsed ← (parseUtf8 source).mapError .frontend
  parsed.run.mapError .validation

end Silmaril.Languages.Starlark.Frontend.Module
