module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Assignment (LexicalBlock)
open Functions (Declaration DeclarationId Program)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr

/-- The evidence for a single definition site, including the child's
whole-block binder order and the independently selected free references. -/
structure Site (parent : LexicalBlock) where
  name : String
  target : name ∈ parent.owned
  parameters : Parameters
  source : Statement
  binders : List String
  locals : List String
  collects : Block.BodyBinders source binders
  localOrder : Block.LocalBinders parameters.names binders locals
  body : ResolvedBody
  free : List Functions.FreeName
  selects : Selects ⟨parameters.names ++ locals, parent.owned ++ parent.enclosing, parent.globals⟩ body.reads free
  defaults : List PlainPositionalDefault
  lexical : Lexical.Elaborates parent parameters.optional defaults

@[expose] def Site.block {parent : LexicalBlock} (site : Site parent) : LexicalBlock :=
  ⟨site.parameters.names ++ site.locals, parent.owned ++ parent.enclosing, parent.globals⟩

@[expose] def Site.statement {parent : LexicalBlock} (site : Site parent) : Statement :=
  .define site.name site.parameters.source site.source

@[expose] def Site.declaration {parent : LexicalBlock} (site : Site parent) : Declaration :=
  ⟨site.parameters.signature (site.defaults.map PlainPositionalDefault.value),
    site.locals.map fileSlot, site.free, site.body.code⟩

/-- The parent reads defaults at the definition site and supplies the
body's capture demands in first-occurrence order. -/
@[expose] def Site.reads {parent : LexicalBlock} (site : Site parent) : List Binding :=
  site.defaults.flatMap PlainPositionalDefault.reads ++ site.free.map Functions.FreeName.source

abbrev Emissions := List (DeclarationId × Declaration)

/-- Finite derivations descend into both the child suite and the tail.
The child suite emits its descendants first. The parent declaration
then precedes all declarations in the tail of the defining suite. -/
inductive Elaborates : LexicalBlock → Statement → Program → ResolvedBody → Program → Emissions → Prop where
  | straight {block : LexicalBlock} {source : Body.Suite} {code : Functions.Body} {reads : List Binding} {seed : Program} :
      Body.Elaborates block source code reads →
      Elaborates block source.source seed ⟨code, reads⟩ seed []
  | define {parent : LexicalBlock} {leading : List (String × Expr)}
      {leadingCode : List (String × Functions.Lowering.Expr)} {leadingReads : List Binding}
      {rest : Statement} {seed childTable final : Program} {tail : ResolvedBody}
      {descendants remaining : Emissions} (site : Site parent) :
      Body.ElaboratesPrefix parent leading leadingCode leadingReads →
      Elaborates site.block site.source seed site.body childTable descendants →
      Elaborates parent rest (childTable.push site.declaration) tail final remaining →
      Elaborates parent (Body.prependSource leading (.seq site.statement rest)) seed
        ⟨Body.prependCode leadingCode (.seq (.define (fileSlot site.name) childTable.size) tail.code),
          leadingReads ++ (site.reads ++ tail.reads)⟩ final
        (descendants ++ (childTable.size, site.declaration) :: remaining)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
