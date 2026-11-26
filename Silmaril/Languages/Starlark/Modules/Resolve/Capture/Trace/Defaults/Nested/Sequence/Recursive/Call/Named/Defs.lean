module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Defs

public section

namespace Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Assignment (LexicalBlock)
open Functions
open Lists (State)
open Lists.Iteration (Flow)

local notation "Expr" => Lowering.Resolve.SourceExpr
local notation "Value" => Lists.Value

abbrev Bindings := List (Binding × Value)

/-- Keywords are delivered to formal slots in source order. The initial
assignments are the positional prefix and saved defaults are still absent. -/
inductive BindsNames (parameters : List Parameter) :
    Bindings → List (String × Value) → Except Lists.Error Bindings → Prop where
  | done (bound : Bindings) : BindsNames parameters bound [] (.ok bound)
  | unknown {bound : Bindings} {name : String} {value : Value} {rest : List (String × Value)} :
      parameters.find? (fun formal => formal.slot.name == name) = none →
      BindsNames parameters bound ((name, value) :: rest) (.error (.unexpectedKeyword name))
  | conflict {bound : Bindings} {name : String} {value previous : Value} {formal : Parameter}
      {rest : List (String × Value)} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound = some previous →
      BindsNames parameters bound ((name, value) :: rest) (.error (.multipleArgumentValues name))
  | deliver {bound : Bindings} {name : String} {value : Value} {formal : Parameter}
      {rest : List (String × Value)} {result : Except Lists.Error Bindings} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound = none →
      BindsNames parameters ((formal.slot, value) :: bound) rest result →
      BindsNames parameters bound ((name, value) :: rest) result

@[expose] def withDefaults (parameters : List Parameter) (bound saved : Bindings) :
    List (Binding × Option Value) :=
  parameters.map fun formal =>
    (formal.slot, (List.lookup formal.slot bound).orElse fun () => List.lookup formal.slot saved)

/-- Only positional formals count toward positional capacity. Named
delivery can use both classes of formal, and defaults fill the remaining slots. -/
inductive Binds (positional named : List Parameter) (saved : Bindings) (actual : Actual) :
    Except Lists.Error Bindings → Prop where
  | surplus : positional.length < actual.positional.length →
      Binds positional named saved actual (.error (.arity positional.length actual.positional.length))
  | rejected {error : Lists.Error} : actual.positional.length ≤ positional.length →
      BindsNames named ((positional.map Parameter.slot).zip actual.positional) actual.keywords (.error error) →
      Binds positional named saved actual (.error error)
  | missing {bound : Bindings} : actual.positional.length ≤ positional.length →
      BindsNames named ((positional.map Parameter.slot).zip actual.positional) actual.keywords (.ok bound) →
      missingNames (withDefaults named bound saved) ≠ [] →
      Binds positional named saved actual (.error (.missingArguments (missingNames (withDefaults named bound saved))))
  | assigned {bound : Bindings} : actual.positional.length ≤ positional.length →
      BindsNames named ((positional.map Parameter.slot).zip actual.positional) actual.keywords (.ok bound) →
      missingNames (withDefaults named bound saved) = [] →
      Binds positional named saved actual (.ok (savedValues (withDefaults named bound saved)))

/-- Names are preserved by lexical operand resolution. -/
inductive Arguments (block : LexicalBlock) : List (String × Expr) →
    List (String × Lowering.Expr) → List Binding → Prop where
  | nil : Arguments block [] [] []
  | cons {name source code reads tail codes later} :
      Body.Operand block source code reads → Arguments block tail codes later →
      Arguments block ((name, source) :: tail) ((name, code) :: codes) (reads ++ later)

structure Operands (block : LexicalBlock) where
  source : List (String × Expr)
  codes : List (String × Lowering.Expr)
  reads : List Binding
  related : Arguments block source codes reads
  distinct : (source.map Prod.fst).Nodup

@[expose] def Operands.empty {block : LexicalBlock} : Operands block := ⟨[], [], [], .nil, .nil⟩

@[expose] def expression (name : String) (positional : List Lowering.Expr)
    (keywords : List (String × Lowering.Expr)) : Lowering.Expr :=
  .call (Leaf.readOperand (fileSlot name)) positional keywords none none

/-- The flattened successful operand values are partitioned by the
syntactic positional count and paired with the original keyword names. -/
@[expose] def collect (positional : Nat) (keywords : List String) (values : List Value) : Actual :=
  ⟨values.take positional, keywords.zip (values.drop positional)⟩

abbrev SiteBinding {parent : LexicalBlock} {formals : List PlainKeywordParameter}
    (site : Site parent formals) : Call.BindingRule :=
  fun defaults => Binds site.declaration.signature.positional site.declaration.signature.named
    (site.defaultKeys.zip defaults)

abbrev RunsWith {parent : LexicalBlock} {formals : List PlainKeywordParameter} (site : Site parent formals) (bodyRuns : State → Lists.Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (name : String)
    (arguments : List Expr) (codes : List Lowering.Expr) (keywords : List (String × Expr))
    (compiled : List (String × Lowering.Expr)) :=
  Call.RunsPacked site bodyRuns block id name (arguments ++ keywords.map Prod.snd) (codes ++ compiled.map Prod.snd)
    (collect codes.length (compiled.map Prod.fst)) (SiteBinding site)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
