module

import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms
public import Silmaril.Logic.Temporal.TLA.Resolution.Names
meta import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! Checked parser-to-denotation regressions for the collection forms. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples

open Resolution Data.Tagged

private meta def noPrimitives : ExternalSignature := fun _ => none

private meta def participantsId : BindingId := .declared ⟨"client", [.unit 0, .member 0]⟩

private meta def source := r#"---- MODULE CollectionChecks ----
CONSTANT p
Build == [k \in p |-> [key |-> k, ready |-> TRUE]]
RecordTypes == [key : {TRUE}, ready : BOOLEAN]
FunctionTypes == [p -> RecordTypes]
BadBound == [i \in TRUE |-> i]
BadRange == [p -> TRUE]
BadFields == [ok : BOOLEAN, bad : TRUE]
BadDomain == [TRUE -> BOOLEAN]
====
"#

private meta def registryFor (text : String) : Except String CheckedRegistry := do
  let parsed ← (Surface.Parser.parseModule text).mapError reprStr
  (Resolution.resolve [("client", .parsed parsed [])] "client").mapError reprStr

private meta def select (registry : CheckedRegistry) (name : String) : Except String BindingId := do
  let some binding := (registry.moduleAt registry.root).bind (·.bindingAt (.ident name))
    | throw s!"missing definition {name}"
  return binding.id

private meta def lower (name : String) : Except String (CheckedExpr noPrimitives .collections) := do
  let registry ← registryFor source
  let id ← select registry name
  (Collections.lowerState registry [] noPrimitives 40 id).mapError reprStr

private meta def rejects (definition : String) (path : Path) (kind : DiagnosticKind) : Bool :=
  let result := do
    let registry ← registryFor s!"---- MODULE Rejected ----\nOut == {definition}\n===="
    let id ← select registry "Out"
    return Collections.lowerState registry [] noPrimitives 40 id
  match result with
  | .ok (.error (.lowering diagnostic)) => diagnostic = ⟨⟨"client", .unit 0 :: .body :: path⟩, kind⟩
  | _ => false

#guard rejects "[a |-> TRUE, a |-> FALSE]" [.field 1] (.duplicateField "a")
#guard rejects "[a : BOOLEAN, a : {TRUE}]" [.field 1] (.duplicateField "a")
#guard rejects "[i, j \\in BOOLEAN |-> i]" [.bound 0] (.unsupported .functionBounds)
#guard rejects "[i \\in BOOLEAN, j \\in BOOLEAN |-> i]" [] (.unsupported .functionBounds)
#guard rejects "[<<i, j>> \\in BOOLEAN |-> i]" [.bound 0] (.unsupported .tupleBinder)
#guard rejects "[a |-> <<TRUE>>]" [.field 0] (.unsupported .tuple)
#guard rejects "[a |-> TRUE][TRUE]" [] (.unsupported .index)

#guard match registryFor source with
  | .ok registry =>
    match Endpoints.lowerState registry [] noPrimitives 40 (.declared ⟨"client", [.unit 1]⟩) with
    | .error (.lowering diagnostic) =>
      diagnostic = ⟨⟨"client", [.unit 1, .body]⟩, .unsupported .function⟩
    | _ => false
  | _ => false

#guard match lower "Build" with
  | .ok checked =>
    match checked.term with
    | .function _ site binder slot (.rigid domain) (.record _ bodySite [("key", .witness use), _]) =>
      site = ⟨"client", [.unit 1, .body]⟩ ∧
        binder = .declared (site.child (.bound 0) |>.child (.binder 0)) ∧
        bodySite = site.child .body ∧ domain = participantsId ∧ slot = use
    | _ => false
  | _ => false

meta section

open Lean

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId

-- Stage the actual expansion. The kernel checks the quoted syntax and its scope.
private partial def quoteTerm (term : Term noPrimitives .collections) :
    Elab.Term.TermElabM Lean.Expr := do
  let initial := fun ctor => mkApp2 (mkConst ctor) (mkConst ``noPrimitives)
    (mkConst ``Fragment.collections)
  let type := initial ``Term
  let node := fun name args => mkAppN (initial name) args
  let enabled ← Meta.mkEqRefl (mkConst ``Fragment.collections)
  let fields := fun (values : List (String × Term noPrimitives .collections)) => do
    let pair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) type
    Meta.mkListLit pair (← values.mapM fun (name, value) => do
      return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) type (toExpr name) (← quoteTerm value))
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .witness slot => return node ``Term.witness #[toExpr slot]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .booleanSet => return node ``Term.booleanSet #[]
  | .enum values => return node ``Term.enum #[← Meta.mkListLit type (← values.mapM quoteTerm)]
  | .function _ site binder slot domain body =>
    return node ``Term.function #[enabled, toExpr site, toExpr binder, toExpr slot,
      ← quoteTerm domain, ← quoteTerm body]
  | .functionSet _ site domain range =>
    return node ``Term.functionSet #[enabled, toExpr site, ← quoteTerm domain, ← quoteTerm range]
  | .record _ site values => return node ``Term.record #[enabled, toExpr site, ← fields values]
  | .recordSet _ site values => return node ``Term.recordSet #[enabled, toExpr site, ← fields values]
  | other => throwError "unexpected expanded term: {reprStr other}"

private def emit (name : String) : Elab.Term.TermElabM Lean.Expr := do
  match lower name with
  | .error message => throwError "{message}"
  | .ok checked =>
    return mkApp4 (mkConst ``CheckedExpr.mk) (mkConst ``noPrimitives) (mkConst ``Fragment.collections)
      (← quoteTerm checked.term) (← Meta.mkEqRefl (toExpr true))

end

private noncomputable def build : CheckedExpr noPrimitives .collections := by_elab emit "Build"
private noncomputable def recordTypes : CheckedExpr noPrimitives .collections := by_elab emit "RecordTypes"
private noncomputable def functionTypes : CheckedExpr noPrimitives .collections := by_elab emit "FunctionTypes"
private noncomputable def badBound : CheckedExpr noPrimitives .collections := by_elab emit "BadBound"
private noncomputable def badRange : CheckedExpr noPrimitives .collections := by_elab emit "BadRange"
private noncomputable def badFields : CheckedExpr noPrimitives .collections := by_elab emit "BadFields"
private noncomputable def badDomain : CheckedExpr noPrimitives .collections := by_elab emit "BadDomain"

universe u
variable (policy : Tagged.Policy.{u}) (invalid : Tagged.CollectionPolicy.{u})

private def noExternal : ExternalInterpretation Value.{u} noPrimitives :=
  fun _ _ impossible => nomatch impossible

private noncomputable def valuation (domain : SetData.{u}) : Valuation Value.{u} :=
  ⟨fun id => if id = participantsId then .set domain else .boolean false, fun _ => .boolean false⟩

private noncomputable def evaluate (expr : CheckedExpr noPrimitives .collections)
    (domain : SetData.{u}) : Value.{u} :=
  expr.eval (policy.collectionOperations invalid) policy.booleans noExternal (valuation domain)

private noncomputable def recordBody (invalid : Tagged.CollectionPolicy.{u}) (key : Value.{u})
    (field : String) : Value.{u} :=
  let fields := [("key", key), ("ready", Value.boolean true)]
  (fields.lookup field).getD (invalid (.record fields))

private theorem build_eq (domain : SetData.{u}) :
    evaluate policy invalid build domain =
      .function (Graph.ofFn domain fun x => .record ["key", "ready"] (recordBody invalid x)) := by
  simp [evaluate, CheckedExpr.eval, build, Term.eval, Term.evalFields, Operations.collection,
    Tagged.Policy.collectionOperations, valuation, participantsId, withWitness, Tagged.Policy.booleans]
  rfl

private theorem built_graph (domain : SetData.{u}) :
    ∃ g : Graph.{u}, evaluate policy invalid build domain = .function g ∧
      g.domain = domain ∧ ∀ key, domain.mem key →
        ∃ r : Graph.{u}, g.lookup key = some (.function r) ∧
          r.domain = SetData.enum [Value.string "key", Value.string "ready"] ∧
          r.lookup (.string "key") = some key ∧ r.lookup (.string "ready") = some (.boolean true) := by
  rw [build_eq]
  refine ⟨_, rfl, Graph.domain_ofFn _ _, ?_⟩
  intro key hk
  refine ⟨_, Graph.lookup_ofFn hk, Graph.domain_record _ _, ?_, ?_⟩
  · exact Graph.lookup_record (recordBody invalid key) (name := "key") (by simp)
  · exact Graph.lookup_record (recordBody invalid key) (name := "ready") (by simp)

private def trueSet : SetData.{u} := SetData.enum [Value.boolean true]
private def boolSet : SetData.{u} := SetData.enum [Value.boolean true, Value.boolean false]

private def fieldSets : List (String × SetData.{u}) := [("key", trueSet), ("ready", boolSet)]

private theorem recordTypes_eq (domain : SetData.{u}) :
    evaluate policy invalid recordTypes domain = .set (SetData.recordSet fieldSets) := by
  simp [evaluate, CheckedExpr.eval, recordTypes, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, fieldSets, trueSet, boolSet, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map]

private theorem functionTypes_eq (domain : SetData.{u}) :
    evaluate policy invalid functionTypes domain =
      .set (domain.functionSet (SetData.recordSet fieldSets)) := by
  simp [evaluate, CheckedExpr.eval, functionTypes, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, valuation, participantsId, fieldSets, trueSet, boolSet, Value.recordSet,
    Value.checkRecordSetFields, Value.decodeRecordSetBounds, Except.map]

private theorem recognizes_record (domain : SetData.{u}) (g : Graph.{u}) :
    (Value.function g).mem (evaluate policy invalid recordTypes domain) ↔
      g.domain = SetData.enum [Value.string "key", Value.string "ready"] ∧
      g.lookup (.string "key") = some (.boolean true) ∧
      ∃ b : Bool, g.lookup (.string "ready") = some (.boolean b) := by
  rw [recordTypes_eq, Value.mem_set, SetData.mem_recordSet]
  simp only [Value.function_injective.eq_iff, exists_eq_left]
  constructor
  · rintro ⟨hd, fits⟩
    obtain ⟨key, hkey, htrue⟩ := fits "key" trueSet (by simp [fieldSets])
    obtain ⟨ready, hready, hbool⟩ := fits "ready" boolSet (by simp [fieldSets])
    simp [trueSet, SetData.mem_enum] at htrue
    refine ⟨hd, htrue ▸ hkey, ?_⟩
    simp [boolSet, SetData.mem_enum] at hbool
    rcases hbool with h | h
    · exact ⟨true, h ▸ hready⟩
    · exact ⟨false, h ▸ hready⟩
  · rintro ⟨hd, hkey, b, hready⟩
    refine ⟨hd, ?_⟩
    intro name bound h
    simp only [fieldSets, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h
    · cases h
      exact ⟨_, hkey, by simp [trueSet, SetData.mem_enum]⟩
    · cases h
      exact ⟨_, hready, by cases b <;> simp [boolSet, SetData.mem_enum]⟩

private theorem recognizes_function (domain : SetData.{u}) (candidate : Value.{u}) :
    candidate.mem (evaluate policy invalid functionTypes domain) ↔
      ∃ g : Graph.{u}, .function g = candidate ∧ g.domain = domain ∧
        ∀ key value, g.relates key value → value.mem (evaluate policy invalid recordTypes domain) := by
  rw [functionTypes_eq, recordTypes_eq, Value.mem_set, SetData.mem_functionSet]
  simp only [Value.mem_set]

private theorem invalid_bound (domain : SetData.{u}) :
    evaluate policy invalid badBound domain = invalid (.function (.boolean true)) := by
  simp [evaluate, CheckedExpr.eval, badBound, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.booleans]

private theorem invalid_range (domain : SetData.{u}) :
    evaluate policy invalid badRange domain = invalid (.functionSet (.set domain) (.boolean true)) := by
  simp [evaluate, CheckedExpr.eval, badRange, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.booleans, valuation, participantsId]

private theorem invalid_domain (domain : SetData.{u}) :
    evaluate policy invalid badDomain domain = invalid (.functionSet (.boolean true) (.set boolSet)) := by
  simp [evaluate, CheckedExpr.eval, badDomain, Term.eval, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.operations, Tagged.Policy.booleans, boolSet]

private theorem invalid_fields (domain : SetData.{u}) :
    evaluate policy invalid badFields domain =
      invalid (.recordSet (.nonSetBound "bad") [("ok", .set boolSet), ("bad", .boolean true)]) := by
  simp [evaluate, CheckedExpr.eval, badFields, Term.eval, Term.evalFields, Operations.collection,
    Tagged.Policy.collectionOperations, Tagged.Policy.operations, Tagged.Policy.booleans, boolSet,
    Value.recordSet, Value.checkRecordSetFields, Value.decodeRecordSetBounds, Except.map]

end Silmaril.Logic.Temporal.TLA.DataElab.Collections.Examples
