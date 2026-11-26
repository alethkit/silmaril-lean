module

public import Silmaril.Languages.Starlark.Modules.Resolve.Assignment.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Block

open Assignment (InOrder LexicalBlock TargetShape)

local notation "Operand" => Functions.Lowering.Resolve.SourceExpr

/-- A target declares exactly the names at its lexical leaves. Receivers
and indices, like RHSs, only contribute reads. -/
abbrev TargetBinders (scope : Scope) (target : Operand) (names : List String) : Prop :=
  ∃ pattern, TargetShape scope target (pattern, names)

/-- Declarations of one command in a load-free module block. A function's
name belongs to this block and its parameters and body belong to another. -/
inductive CommandBinders : Command → List String → Prop where
  | assign (name : String) (rhs : Operand) : CommandBinders (.assign name rhs) [name]
  | pattern {target : Operand} {rhs : CompExpr} {names : List String} :
      TargetBinders .global target names → CommandBinders (.assignTargetCompExpr target rhs) names
  | store (receiver index rhs : Operand) : CommandBinders (.setIndex receiver index rhs) []
  | eval (value : Operand) : CommandBinders (.eval value) []
  | define (name : String) (signature : SourceSignature) (body : Statement) :
      CommandBinders (.define name signature body) [name]

inductive ModuleBinders : List Command → List String → Prop where
  | nil : ModuleBinders [] []
  | cons {first : Command} {rest : List Command} {head tail : List String} :
      CommandBinders first head → ModuleBinders rest tail → ModuleBinders (first :: rest) (head ++ tail)

/-- The current function block includes both arms of a branch and both
parts of a sequence. Enter a nested definition separately when collecting
its parameters and body. -/
inductive BodyBinders : Statement → List String → Prop where
  | pass : BodyBinders .pass []
  | assign (name : String) (rhs : Operand) : BodyBinders (.assign name rhs) [name]
  | pattern {target : Operand} {rhs : CompExpr} {names : List String} :
      TargetBinders .local target names → BodyBinders (.assignTargetCompExpr target rhs) names
  | store (receiver index rhs : Operand) : BodyBinders (.setIndex receiver index rhs) []
  | eval (value : Operand) : BodyBinders (.eval value) []
  | ret (value : Option Operand) : BodyBinders (.ret value) []
  | seq {first rest : Statement} {head tail : List String} :
      BodyBinders first head → BodyBinders rest tail → BodyBinders (.seq first rest) (head ++ tail)
  | branch {test : Operand} {yes no : Statement} {left right : List String} :
      BodyBinders yes left → BodyBinders no right → BodyBinders (.branch test yes no) (left ++ right)
  | define (name : String) (signature : SourceSignature) (body : Statement) :
      BodyBinders (.define name signature body) [name]

/-- Parameter declarations in normalized signature order. Defaults play no
role in this judgment. They are resolved in the parent by a different phase. -/
inductive ParameterBinders : SourceSignature → List String → Prop where
  | signature {positional keywords : List SourceParameter} {posNames keyNames : List String}
      (star starStar : Option String) :
      InOrder (fun parameter name => parameter.name = name) positional posNames →
      InOrder (fun parameter name => parameter.name = name) keywords keyNames →
      ParameterBinders ⟨positional, keywords, star, starStar⟩
        (posNames ++ keyNames ++ star.toList ++ starStar.toList)

/-- Keep the first occurrence of each local name that has no parameter slot.
Once considered, a name's later occurrences cannot introduce another slot. -/
inductive LocalBinders (parameters : List String) : List String → List String → Prop where
  | nil : LocalBinders parameters [] []
  | skip {first : String} {rest locals : List String} :
      first ∈ parameters → LocalBinders parameters (rest.filter fun later => !(later == first)) locals →
      LocalBinders parameters (first :: rest) locals
  | keep {first : String} {rest locals : List String} :
      first ∉ parameters → LocalBinders parameters (rest.filter fun later => !(later == first)) locals →
      LocalBinders parameters (first :: rest) (first :: locals)

/-- A statement-level assignment site in this function block, including
both branches. This relation never descends into a different function. -/
inductive AssignmentSite (target : Operand) (rhs : CompExpr) : Statement → Prop where
  | here : AssignmentSite target rhs (.assignTargetCompExpr target rhs)
  | first {first rest : Statement} : AssignmentSite target rhs first → AssignmentSite target rhs (.seq first rest)
  | rest {first rest : Statement} : AssignmentSite target rhs rest → AssignmentSite target rhs (.seq first rest)
  | yes {test : Operand} {yes no : Statement} : AssignmentSite target rhs yes →
      AssignmentSite target rhs (.branch test yes no)
  | no {test : Operand} {yes no : Statement} : AssignmentSite target rhs no →
      AssignmentSite target rhs (.branch test yes no)

end Silmaril.Languages.Starlark.Modules.Resolve.Block
