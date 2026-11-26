module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Assignment (LexicalBlock)
open Functions (Declaration DeclarationId Program)

local notation "Expr" => Functions.Lowering.Resolve.SourceExpr

@[expose] def parameterNames (positionals : Parameters) : List PlainKeywordParameter → List String
  | [] => positionals.names
  | first :: rest => positionals.names ++ (first :: rest).map (SourceParameter.name ∘ PlainKeywordParameter.source)

@[expose] def keywordDefaults (keywords : List PlainKeywordParameter) : List PlainPositionalDefault :=
  keywords.filterMap PlainKeywordParameter.default

abbrev KeywordLexical (block : LexicalBlock) (keywords : List PlainKeywordParameter) : Prop :=
  Lexical.Elaborates block ((keywordDefaults keywords).map fun item => (item.name, item.source))
    (keywordDefaults keywords)

/-- The evidence for a single definition site, including the child's
whole-block binder order and the independently selected free references. -/
structure Site (parent : LexicalBlock) (keywords : List PlainKeywordParameter := []) where
  name : String
  target : name ∈ parent.owned
  parameters : Parameters
  source : Statement
  binders : List String
  locals : List String
  collects : Block.BodyBinders source binders
  localOrder : Block.LocalBinders (parameterNames parameters keywords) binders locals
  body : ResolvedBody
  free : List Functions.FreeName
  selects : Selects ⟨parameterNames parameters keywords ++ locals, parent.owned ++ parent.enclosing, parent.globals⟩ body.reads free
  defaults : List PlainPositionalDefault
  lexical : Lexical.Elaborates parent parameters.optional defaults

@[expose] def Site.block {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : LexicalBlock :=
  ⟨parameterNames site.parameters keywords ++ site.locals, parent.owned ++ parent.enclosing, parent.globals⟩

@[expose] def Site.sourceSignature {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : SourceSignature :=
  { site.parameters.source with keywordOnly := keywords.map PlainKeywordParameter.source }

@[expose] def Site.statement {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : Statement :=
  .define site.name site.sourceSignature site.source

@[expose] def Site.declaration {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : Declaration :=
  let signature := site.parameters.signature (site.defaults.map PlainPositionalDefault.value)
  ⟨{ signature with keywordOnly := keywords.map PlainKeywordParameter.resolved },
    site.locals.map fileSlot, site.free, site.body.code⟩

@[expose] def Site.defaultSources {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : List (String × Expr) :=
  match keywords with
  | [] => site.parameters.optional
  | first :: rest => site.parameters.optional ++ (keywordDefaults (first :: rest)).map (fun item => (item.name, item.source))

@[expose] def Site.defaultKeys {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : List Binding :=
  site.defaultSources.map (fileSlot ∘ Prod.fst)

@[expose] def Site.defaultsInOrder {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : List PlainPositionalDefault :=
  match keywords with
  | [] => site.defaults
  | first :: rest => site.defaults ++ keywordDefaults (first :: rest)

/-- The parent reads defaults at the definition site and supplies the
body's capture demands in first-occurrence order. -/
@[expose] def Site.reads {parent : LexicalBlock} {keywords : List PlainKeywordParameter}
    (site : Site parent keywords) : List Binding :=
  site.defaultsInOrder.flatMap PlainPositionalDefault.reads ++ site.free.map Functions.FreeName.source

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
