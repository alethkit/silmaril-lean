module

public import Silmaril.Project.Registry.Defs

/-!
# Silmaril projects: IR families, subsets and models

A project names a family, the typed program declarations for its subsets, and
the semantic definitions over those programs. Syntax kinds are themselves
project records. The model's semantic reading and its optional reference to
an institution are supplied by the author.
-/

public meta section

namespace Silmaril.Project

open Lean Meta Elab Command

private def requireRecord (kind field target : String) (fs : Fields) : CoreM Unit := do
  let name ← fs.str kind field
  unless (findRecord? (← getEnv) target name).isSome do
    throwError "silmaril {kind}: no `silmaril {target} {name}` is declared or imported"

private def irNamed : Handler where
  mainKey := "title"
  run? := some fun kind name? fs => do
    let _ ← liftCoreM (fs.str kind "title")
    return #[(← liftCoreM (needName kind name?), fs)]

@[silmaril_kind ir_family] def irFamilyHandler : Handler := irNamed
@[silmaril_kind ir_syntax_kind] def irSyntaxKindHandler : Handler := irNamed

@[silmaril_kind ir_subset] def irSubsetHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let decl ← liftCoreM (fs.const kind "decl")
    liftCoreM do
      requireRecord kind "family" "ir_family" fs
      requireRecord kind "syntax_kind" "ir_syntax_kind" fs
      let _ ← fs.str kind "title"
      pure ()
    liftTermElabM do
      forallTelescopeReducing (← constType decl) fun _ result => do
        unless result.isSort && !result.isProp do
          throwError "silmaril {kind}: {decl} must declare a type or a family of types"
    return #[(name, fs)]

/-- Check for a parameter whose type is an instance of the registered program family. -/
private def acceptsPrograms (decl programs : Name) : MetaM Bool := do
  forallTelescopeReducing (← constType decl) fun args _ =>
    args.anyM fun arg => withoutModifyingState do
      let family ← mkConstWithFreshMVarLevels programs
      let (params, _, _) ← forallMetaTelescopeReducing (← inferType family)
      isDefEq (← inferType arg) (mkAppN family params)

@[silmaril_kind ir_model] def irModelHandler : Handler where
  run? := some fun kind name? fs => do
    let name ← liftCoreM (needName kind name?)
    let decl ← liftCoreM (fs.const kind "decl")
    let programs ← liftCoreM do
      let subset ← fs.str kind "subset"
      let reading ← fs.str kind "semantics"
      unless ["operational", "denotational"].contains reading do
        throwError "silmaril {kind}: `semantics` must be operational or denotational"
      let _ ← fs.str kind "title"
      if (fs.get? "institution").isSome then
        requireRecord kind "institution" "institution" fs
      recordDecl kind "ir_subset" subset
    unless ← liftTermElabM (acceptsPrograms decl programs) do
      throwError "silmaril {kind}: {decl} must take a program of type {programs}"
    return #[(name, fs)]

end Silmaril.Project
