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

abbrev Keywords := List (String × Value)

/-- Each explicit keyword is delivered to a named formal if one exists.
Unmatched values go to the keyword collector in encounter order. -/
inductive BindsNames (parameters : List Parameter) (kwargs : Option Binding) :
    Bindings × Keywords → Keywords → Except Lists.Error (Bindings × Keywords) → Prop where
  | done (bound : Bindings × Keywords) : BindsNames parameters kwargs bound [] (.ok bound)
  | unknown {bound : Bindings × Keywords} {name : String} {value : Value} {rest : Keywords} :
      kwargs = none →
      parameters.find? (fun formal => formal.slot.name == name) = none →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.unexpectedKeyword name))
  | conflict {bound : Bindings × Keywords} {name : String} {value previous : Value} {formal : Parameter}
      {rest : Keywords} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound.1 = some previous →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.multipleArgumentValues name))
  | deliver {bound : Bindings × Keywords} {name : String} {value : Value} {formal : Parameter}
      {rest : Keywords} {result : Except Lists.Error (Bindings × Keywords)} :
      parameters.find? (fun item => item.slot.name == name) = some formal →
      List.lookup formal.slot bound.1 = none →
      BindsNames parameters kwargs ((formal.slot, value) :: bound.1, bound.2) rest result →
      BindsNames parameters kwargs bound ((name, value) :: rest) result
  | repeated {bound : Bindings × Keywords} {name : String} {value previous : Value} {slot : Binding}
      {rest : Keywords} :
      kwargs = some slot →
      parameters.find? (fun item => item.slot.name == name) = none →
      List.lookup name bound.2 = some previous →
      BindsNames parameters kwargs bound ((name, value) :: rest) (.error (.multipleArgumentValues name))
  | collect {bound : Bindings × Keywords} {name : String} {value : Value} {slot : Binding}
      {rest : Keywords} {result : Except Lists.Error (Bindings × Keywords)} :
      kwargs = some slot →
      parameters.find? (fun item => item.slot.name == name) = none →
      List.lookup name bound.2 = none →
      BindsNames parameters kwargs (bound.1, bound.2 ++ [(name, value)]) rest result →
      BindsNames parameters kwargs bound ((name, value) :: rest) result

@[expose] def withDefaults (parameters : List Parameter) (bound saved : Bindings) :
    List (Binding × Option Value) :=
  parameters.map fun formal =>
    (formal.slot, (List.lookup formal.slot bound).orElse fun () => List.lookup formal.slot saved)

/-- The positional prefix has fixed capacity when no collector is present. -/
@[expose] def Fits (varargs : Option Binding) (parameters : List Parameter) (actual : Actual) : Prop :=
  varargs = none → actual.positional.length ≤ parameters.length

/-- Both surpluses are recorded during binding. Missing required
parameters reject before either collector can allocate. -/
inductive Binds (positional named : List Parameter) (varargs kwargs : Option Binding) (saved : Bindings)
    (actual : Actual) : Except Lists.Error BoundArguments → Prop where
  | surplus : varargs = none → positional.length < actual.positional.length →
      Binds positional named varargs kwargs saved actual (.error (.arity positional.length actual.positional.length))
  | rejected {error : Lists.Error} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.error error) →
      Binds positional named varargs kwargs saved actual (.error error)
  | missing {bound : Bindings} {extras : Keywords} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.ok (bound, extras)) →
      missingNames (withDefaults named bound saved) ≠ [] →
      Binds positional named varargs kwargs saved actual
        (.error (.missingArguments (missingNames (withDefaults named bound saved))))
  | assigned {bound : Bindings} {extras : Keywords} : Fits varargs positional actual →
      BindsNames named kwargs ((positional.map Parameter.slot).zip actual.positional, [])
        actual.keywords (.ok (bound, extras)) →
      missingNames (withDefaults named bound saved) = [] →
      Binds positional named varargs kwargs saved actual
        (.ok ⟨savedValues (withDefaults named bound saved),
          actual.positional.drop positional.length, extras⟩)

@[expose] def keywordEntries (keywords : Keywords) : List Lists.Entry :=
  keywords.map fun (name, value) => ⟨.string name, [.string name], value⟩

inductive PacksPositionals : Option Binding → State → BoundArguments → Bindings → State → Prop where
  | ordinary (caller : State) (bound : BoundArguments) : PacksPositionals none caller bound bound.named caller
  | tuple {slot : Binding} {caller packed : State} {bound : BoundArguments} {tuple : Value} :
      Lists.allocateTuple bound.surplusPositional caller = .ok tuple packed →
      PacksPositionals (some slot) caller bound ((slot, tuple) :: bound.named) packed

inductive PacksKeywords : Option Binding → State → Keywords → Bindings → Bindings → State → Prop where
  | ordinary (caller : State) (extras : Keywords) (assigned : Bindings) :
      PacksKeywords none caller extras assigned assigned caller
  | dict {slot : Binding} {caller packed : State} {extras : Keywords} {assigned : Bindings} {dictionary : Value} :
      Lists.allocateDict (keywordEntries extras) caller = .ok dictionary packed →
      PacksKeywords (some slot) caller extras assigned ((slot, dictionary) :: assigned) packed

/-- The positional pack precedes the keyword pack and both precede activation. -/
abbrev Packs (varargs kwargs : Option Binding) (caller : State) (bound : BoundArguments)
    (assigned : Bindings) (packed : State) : Prop :=
  ∃ positional middle, PacksPositionals varargs caller bound positional middle ∧
    PacksKeywords kwargs middle bound.surplusKeywords positional assigned packed

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

abbrev SiteBinding {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) : Call.BindingRule BoundArguments :=
  fun defaults => Binds site.declaration.signature.positional site.declaration.signature.named
    site.declaration.signature.varargs site.declaration.signature.kwargs (site.defaultKeys.zip defaults)

abbrev RunsWith {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) (bodyRuns : State → Lists.Outcome Flow → Prop)
    (block : LexicalBlock) (id : DeclarationId) (name : String)
    (arguments : List Expr) (codes : List Lowering.Expr) (keywords : List (String × Expr))
    (compiled : List (String × Lowering.Expr)) :=
  Call.RunsPacked site bodyRuns block id name (arguments ++ keywords.map Prod.snd) (codes ++ compiled.map Prod.snd)
    (collect codes.length (compiled.map Prod.fst)) (SiteBinding site)
    (Packs site.declaration.signature.varargs site.declaration.signature.kwargs)

end Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
