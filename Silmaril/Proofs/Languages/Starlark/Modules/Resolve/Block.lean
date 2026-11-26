module

public import Silmaril.Languages.Starlark.Modules.Resolve.Block.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block

open Silmaril.Languages.Starlark (Scope)
open Silmaril.Languages.Starlark.Modules (globalSlot fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment
open Silmaril.Languages.Starlark.Modules.Resolve.Block
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (Context resolveReadValue)

local notation "Operand" => Silmaril.Languages.Starlark.Functions.Lowering.Resolve.SourceExpr

theorem module_names {commands : List Command} {names : List String}
    (declared : ModuleBinders commands names) :
    globalNames commands = names ∧ fileNames commands = [] := by
  induction declared with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases head with
    | pattern shape =>
      obtain ⟨_, related⟩ := shape
      have parsed : parseAssignmentPattern globalSlot _ = _ :=
        parseAssignmentPattern_complete _ _ _ related
      simp [globalNames, fileNames] at ih
      exact ⟨by simp [globalNames, parsed, ih.1] <;> rfl, by simpa [fileNames] using ih.2⟩
    | _ =>
      simp [globalNames, fileNames] at ih
      exact ⟨by simp [globalNames, ih.1], by simpa [fileNames] using ih.2⟩

theorem body_names {body : Statement} {names : List String} (declared : BodyBinders body names) :
    body.localNames = .ok names := by
  induction declared with
  | pattern shape =>
    obtain ⟨_, related⟩ := shape
    have parsed : parseAssignmentPattern fileSlot _ = _ :=
      parseAssignmentPattern_complete _ _ _ related
    simp [Statement.localNames, parsed] <;> rfl
  | seq _ _ first second | branch _ _ first second =>
    simp [Statement.localNames, first, second, bind, Except.bind, pure, Except.pure]
  | _ => rfl

private theorem names_map {parameters : List SourceParameter} {names : List String}
    (related : InOrder (fun parameter name => parameter.name = name) parameters names) :
    parameters.map SourceParameter.name = names := by
  induction related with
  | nil => rfl
  | cons head _ ih => simp [head, ih]

theorem parameter_names {signature : SourceSignature} {names : List String}
    (declared : ParameterBinders signature names) : signature.parameterNames = names := by
  cases declared with
  | signature star starStar positional keywords =>
    simp [SourceSignature.parameterNames, names_map positional, names_map keywords]

theorem local_names {parameters occurrences locals : List String}
    (declared : LocalBinders parameters occurrences locals) :
    occurrences.eraseDups.filter (!parameters.contains ·) = locals := by
  induction declared with
  | nil => rfl
  | skip member _ ih => simpa [List.eraseDups_cons, member] using ih
  | keep absent _ ih => simp [List.eraseDups_cons, absent] <;> simpa using ih

theorem module_block {commands : List Command} {names : List String} (declared : ModuleBinders commands names) :
    moduleBlock commands = ⟨(LexicalBlock.mk [] [] names).context, .global⟩ := by
  simp [moduleBlock, (module_names declared).1, (module_names declared).2, LexicalBlock.context]

theorem function_layout (parent : Context) {signature : SourceSignature} {body : Statement}
    {parameters occurrences locals : List String}
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) :
    collectFunctionLayout parent signature body =
      .ok ⟨locals, ⟨(LexicalBlock.mk (parameters ++ locals) parent.locals parent.globals).context, .local⟩⟩ := by
  simp only [collectFunctionLayout, body_names bodyDecls, functionLayout, parameter_names parameterDecls,
    local_names localDecls, LexicalBlock.context, Except.map]

private theorem module_site {commands : List Command} {globals : List String} {target : Operand} {rhs : CompExpr}
    (declared : ModuleBinders commands globals) (site : Command.assignTargetCompExpr target rhs ∈ commands) :
    ∃ names, TargetBinders .global target names ∧ names ⊆ globals := by
  induction declared with
  | nil => simp at site
  | cons head tail ih =>
    rcases List.mem_cons.mp site with rfl | site
    · cases head with
      | pattern shape => exact ⟨_, shape, List.subset_append_left _ _⟩
    · obtain ⟨_, shape, memberOf⟩ := ih site
      exact ⟨_, shape, fun _ member => List.mem_append_right _ (memberOf member)⟩

private theorem body_site {body : Statement} {occurrences : List String} {target : Operand} {rhs : CompExpr}
    (declared : BodyBinders body occurrences) (site : AssignmentSite target rhs body) :
    ∃ names, TargetBinders .local target names ∧ names ⊆ occurrences := by
  induction site generalizing occurrences with
  | here =>
    cases declared with
    | pattern shape => exact ⟨_, shape, fun _ member => member⟩
  | first _ ih =>
    cases declared with
    | seq left _ =>
      obtain ⟨_, shape, memberOf⟩ := ih left
      exact ⟨_, shape, fun _ member => List.mem_append_left _ (memberOf member)⟩
  | rest _ ih =>
    cases declared with
    | seq _ right =>
      obtain ⟨_, shape, memberOf⟩ := ih right
      exact ⟨_, shape, fun _ member => List.mem_append_right _ (memberOf member)⟩
  | yes _ ih =>
    cases declared with
    | branch left _ =>
      obtain ⟨_, shape, memberOf⟩ := ih left
      exact ⟨_, shape, fun _ member => List.mem_append_left _ (memberOf member)⟩
  | no _ ih =>
    cases declared with
    | branch _ right =>
      obtain ⟨_, shape, memberOf⟩ := ih right
      exact ⟨_, shape, fun _ member => List.mem_append_right _ (memberOf member)⟩

private theorem target_binders_unique {scope : Scope} {target : Operand} {first second : List String}
    (firstDecl : TargetBinders scope target first) (secondDecl : TargetBinders scope target second) :
    first = second := by
  obtain ⟨firstShape, firstDecl⟩ := firstDecl
  obtain ⟨secondShape, secondDecl⟩ := secondDecl
  have equal := (parseAssignmentPattern_complete _ _ _ firstDecl).symm.trans
    (parseAssignmentPattern_complete _ _ _ secondDecl)
  exact congrArg Prod.snd (Except.ok.inj equal)

theorem local_binders_exist (parameters occurrences : List String) :
    ∃ locals, LocalBinders parameters occurrences locals := by
  induction occurrences using (measure (List.length : List String → Nat)).wf.induction with
  | h occurrences ih =>
    cases occurrences with
    | nil => exact ⟨[], .nil⟩
    | cons first rest =>
      obtain ⟨_, remaining⟩ := ih (rest.filter fun later => !(later == first))
        (Nat.lt_succ_of_le (List.length_filter_le _ _))
      by_cases parameter : first ∈ parameters
      · exact ⟨_, .skip parameter remaining⟩
      · exact ⟨_, .keep parameter remaining⟩

theorem function_owns_declared {parameters occurrences locals : List String}
    (declared : LocalBinders parameters occurrences locals) {name : String} (member : name ∈ occurrences) :
    name ∈ parameters ++ locals := by
  rw [List.mem_append, ← local_names declared]
  by_cases parameter : name ∈ parameters
  · exact Or.inl parameter
  · exact Or.inr (by simp [parameter, member, List.mem_eraseDups])

theorem resolve_owned_read (parent : Context) {signature : SourceSignature} {body : Statement}
    {parameters occurrences locals : List String}
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) (name : String)
    (legal : name.toList.head? ≠ some '$') (member : name ∈ parameters ∨ name ∈ occurrences) :
    (do
      let layout ← collectFunctionLayout parent signature body
      (resolveReadValue layout.block.reads name).mapError Error.expression) =
      .ok (.atom (.read (.bound (fileSlot name))), some (fileSlot name)) := by
  rw [function_layout parent parameterDecls bodyDecls localDecls]
  have owned := member.elim (List.mem_append_left locals) (function_owns_declared localDecls)
  have inContext : name ∈ parameters ∨ name ∈ locals ∨ name ∈ parent.locals := by
    simpa [List.mem_append, or_assoc] using (List.mem_append_left parent.locals owned)
  simp [resolveReadValue, Silmaril.Languages.Starlark.resolveName, LexicalBlock.context, legal, inContext,
    bind, Except.bind, Except.mapError, fileSlot]


theorem module_assignment (commands : List Command) (globals : List String)
    (declared : ModuleBinders commands globals) (target : Operand) (rhs : CompExpr)
    (site : Command.assignTargetCompExpr target rhs ∈ commands)
    (targetProfile : TargetInProfile .global target) (rhsProfile : RhsInProfile rhs)
    (program next : Program) (result : ResolvedPatternAssignment)
    (ran : elaboratePatternAssignment (moduleBlock commands).reads (moduleBlock commands).writes
      target rhs program = .ok (result, next)) :
    AssignmentResolves ⟨[], [], globals⟩ .global target rhs result ∧ result.names ⊆ globals ∧ next = program := by
  rw [module_block declared] at ran
  obtain ⟨related, table⟩ := assignment_sound _ _ target rhs program next result targetProfile rhsProfile ran
  obtain ⟨_, shape, _⟩ := related.targetResolves
  obtain ⟨names, declared, memberOf⟩ := module_site declared site
  have equal := target_binders_unique ⟨_, shape⟩ declared
  exact ⟨related, equal ▸ memberOf, table⟩

theorem function_assignment (parent : Context) (signature : SourceSignature) (body : Statement)
    (parameters occurrences locals : List String)
    (parameterDecls : ParameterBinders signature parameters) (bodyDecls : BodyBinders body occurrences)
    (localDecls : LocalBinders parameters occurrences locals) (target : Operand) (rhs : CompExpr)
    (site : AssignmentSite target rhs body) (targetProfile : TargetInProfile .local target)
    (rhsProfile : RhsInProfile rhs) (program next : Program) (result : ResolvedPatternAssignment)
    (ran : (do
      let layout ← collectFunctionLayout parent signature body
      elaboratePatternAssignment layout.block.reads layout.block.writes target rhs program) = .ok (result, next)) :
    AssignmentResolves ⟨parameters ++ locals, parent.locals, parent.globals⟩ .local target rhs result ∧
      result.names ⊆ parameters ++ locals ∧ next = program := by
  rw [function_layout parent parameterDecls bodyDecls localDecls] at ran
  obtain ⟨related, table⟩ := assignment_sound _ _ target rhs program next result targetProfile rhsProfile ran
  obtain ⟨_, shape, _⟩ := related.targetResolves
  obtain ⟨names, declared, memberOf⟩ := body_site bodyDecls site
  have equal := target_binders_unique ⟨_, shape⟩ declared
  exact ⟨related, fun _ member => function_owns_declared localDecls (memberOf (equal ▸ member)), table⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block
