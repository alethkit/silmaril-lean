module

public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Block

open Assignment
open Functions (Program)
open Functions.Lowering.Resolve (Context resolveReadValue)

local notation "Operand" => Functions.Lowering.Resolve.SourceExpr

/-- A load-free module collects its declared names in command order. -/
theorem moduleBlock_eq {commands : List Command} {globals : List String}
    (declared : ModuleBinders commands globals) :
    moduleBlock commands = ⟨(LexicalBlock.mk [] [] globals).context, .global⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.module_block declared

/-- The function collector visits the entire current lexical block. -/
theorem localNames_eq {body : Statement} {names : List String} (declared : BodyBinders body names) :
    body.localNames = .ok names :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.body_names declared

theorem localBinders_exists (parameters occurrences : List String) :
    ∃ locals, LocalBinders parameters occurrences locals :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.local_binders_exist parameters occurrences

/-- Parameters and the first occurrences of other binders determine the
function's local slots. Its enclosing locals and globals come from the parent. -/
theorem collectFunctionLayout_eq (parent : Context) {signature : SourceSignature} {body : Statement}
    {parameters occurrences locals : List String}
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) :
    collectFunctionLayout parent signature body =
      .ok ⟨locals, ⟨(LexicalBlock.mk (parameters ++ locals) parent.locals parent.globals).context, .local⟩⟩ :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.function_layout parent parameterDecls bodyDecls localDecls

/-- Reads of a parameter or body binder select its owned slot throughout
the block, including before the first assignment to a body binder. -/
theorem owned_read (parent : Context) {parameters occurrences locals : List String}
    (declared : LocalBinders parameters occurrences locals) {name : String}
    (member : name ∈ parameters ∨ name ∈ occurrences) :
    ReadResolves ⟨parameters ++ locals, parent.locals, parent.globals⟩ name
      (.atom (.read (.bound (fileSlot name)))) [fileSlot name] :=
  .owned (member.elim (List.mem_append_left locals)
    (Proofs.Languages.Starlark.Modules.Resolve.Block.function_owns_declared declared))

/-- The executable lookup uses the same owned slot even when a prior read
occurs before the assignment that contributed its binder. -/
theorem resolve_owned_read (parent : Context) {signature : SourceSignature} {body : Statement}
    {parameters occurrences locals : List String}
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) (name : String)
    (legal : name.toList.head? ≠ some '$') (member : name ∈ parameters ∨ name ∈ occurrences) :
    (do
      let layout ← collectFunctionLayout parent signature body
      (resolveReadValue layout.block.reads name).mapError Error.expression) =
      .ok (.atom (.read (.bound (fileSlot name))), some (fileSlot name)) :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.resolve_owned_read parent parameterDecls bodyDecls localDecls
    name legal member

/-- The mixed assignment phase uses the module collector's context and
global write scope. Its name leaves belong to the declared globals. -/
theorem module_assignment_sound (commands : List Command) (globals : List String)
    (declared : ModuleBinders commands globals) (target : Operand) (rhs : CompExpr)
    (site : Command.assignTargetCompExpr target rhs ∈ commands)
    (targetProfile : TargetInProfile .global target) (rhsProfile : RhsInProfile rhs)
    (program next : Program) (result : ResolvedPatternAssignment)
    (ran : elaboratePatternAssignment (moduleBlock commands).reads (moduleBlock commands).writes
      target rhs program = .ok (result, next)) :
    AssignmentResolves ⟨[], [], globals⟩ .global target rhs result ∧ result.names ⊆ globals ∧ next = program :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.module_assignment commands globals declared target rhs
    site targetProfile rhsProfile program next result ran

/-- The mixed assignment phase uses the function collector's context and
local write scope. Its name leaves belong to the parameter or local slots. -/
theorem function_assignment_sound (parent : Context) (signature : SourceSignature) (body : Statement)
    (parameters occurrences locals : List String)
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) (target : Operand) (rhs : CompExpr)
    (site : AssignmentSite target rhs body) (targetProfile : TargetInProfile .local target)
    (rhsProfile : RhsInProfile rhs) (program next : Program) (result : ResolvedPatternAssignment)
    (ran : (do
      let layout ← collectFunctionLayout parent signature body
      elaboratePatternAssignment layout.block.reads layout.block.writes target rhs program) = .ok (result, next)) :
    AssignmentResolves ⟨parameters ++ locals, parent.locals, parent.globals⟩ .local target rhs result ∧
      result.names ⊆ parameters ++ locals ∧ next = program :=
  Proofs.Languages.Starlark.Modules.Resolve.Block.function_assignment parent signature body parameters occurrences
    locals parameterDecls bodyDecls localDecls target rhs site targetProfile rhsProfile program next result ran

end Silmaril.Languages.Starlark.Modules.Resolve.Block
