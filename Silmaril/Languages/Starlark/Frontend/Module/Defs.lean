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

private def lowerFunction (fn : ParsedFunction) : Except Diagnostic Modules.Resolve.Command := do
  let body ← fn.body.mapM fun stmt => lowerStmt stmt.span stmt.stmt
  let body := match body.reverse with
    | [] => .pass
    | last :: preceding => preceding.foldl (fun rest first => .seq first rest) last
  return .define fn.name (.required fn.parameters) body

private def lowerCommand (source : LocatedFileCommand) :
    Except Diagnostic (Option LocatedCommand) := do
  let command ← match source.command with
    | .simple .pass => pure none
    | .simple (.assign name rhs) =>
      pure (some (.assign name (← lowerExpr source.span rhs)))
    | .simple (.eval value) => pure (some (.eval (← lowerExpr source.span value)))
    | .simple _ => .error ⟨.unsupported .compoundStatement, source.span⟩
    | .define fn => pure (some (← lowerFunction fn))
    | .assignCall target callee positional => do
      let arguments ← positional.mapM fun item => lowerExpr item.span item.expr
      pure (some (.assign target (.call (.scalar (.read callee)) arguments [] none none)))
  return command.map (⟨source.span, ·⟩)

private def lowerCommands (source : List LocatedFileCommand) : Except Diagnostic ParsedModule := do
  return ⟨(← source.mapM lowerCommand).filterMap id⟩

/-- Parse and normalize a file for the load-free module entry point. -/
def parse (source : String) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFile source)

/-- Parse and normalize original UTF-8 file bytes. -/
def parseUtf8 (source : ByteArray) : Except Diagnostic ParsedModule := do
  lowerCommands (← parseFileUtf8 source)

/-- Initialize and publish a closed module through the normalized module API. -/
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
