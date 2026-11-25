module

import Silmaril.Logic.Temporal.TLA.DataBridge.Thms
public import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Tagged
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import Silmaril.Logic.Temporal.TLA.Data.Tagged.Collections.RecordSet.Thms
meta import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! Selected state semantics of the intact pinned ACP_SB module. -/

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.ACP_SB

open Resolution DataElab Data.Tagged

private meta abbrev root : ModuleId := "pinned/acp-sb"
private meta abbrev declaration (unit : Nat) : BindingId := .declared ⟨root, [.unit unit]⟩
private meta abbrev member (unit index : Nat) : BindingId :=
  .declared ⟨root, [.unit unit, .member index]⟩
private meta def noPrimitives : ExternalSignature := fun _ => none

meta section

open Lean Elab.Term

private def checkedSource : TermElabM Instances.CheckedInstances := do
  let some path ← IO.getEnv "SILMARIL_ACP_SB_SOURCE"
    | throwError "stage ACP_SB with tla-acp-source-acceptance/check.py"
  let source ← match Surface.Parser.parseModule (← IO.FS.readFile path) with
    | .ok source => pure source
    | .error error => throwError "ACP_SB parse: {reprStr error}"
  unless source.name = "ACP_SB" ∧ source.units.length = 40 ∧ source.extendsModules = [] do
    throwError "expected the complete ACP_SB module with no imports"
  let checked ← match Instances.check [(root, .parsed source [])] root with
    | .ok checked => pure checked
    | .error error => throwError "ACP_SB resolution or levels: {reprStr error}"
  let some retained := (checked.registry.moduleAt root).bind (·.source)
    | throwError "missing original ACP_SB source"
  unless reprStr retained = reprStr source do throwError "ACP_SB source changed during checking"
  return checked

private def select (checked : Instances.CheckedInstances) (name : String) (unit : Nat) :
    TermElabM (CheckedExpr noPrimitives .collections) := do
  let id := declaration unit
  let binding := (checked.registry.moduleAt root).bind (·.bindingAt (.ident name))
  let some summary := checked.levels.operatorAt id | throwError "missing level for {name}"
  unless binding.map (·.id) = some id ∧ summary.result = Levels.LevelTerm.fixed .state ∧
      summary.parameters.isEmpty do
    throwError "unexpected declaration identity or level for {name}"
  match Collections.lowerState checked.registry [] noPrimitives 32 id with
  | .ok selected => return selected
  | .error error => throwError "ACP_SB {name} lowering: {reprStr error}"

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId
deriving instance ToExpr for Logic

private partial def quoteTerm (term : Term noPrimitives .collections) : TermElabM Lean.Expr := do
  let ctor := fun name => mkApp2 (mkConst name) (mkConst ``noPrimitives)
    (mkConst ``Fragment.collections)
  let type := ctor ``DataElab.Term
  let node := fun name args => mkAppN (ctor name) args
  let enabled ← Meta.mkEqRefl (mkConst ``Fragment.collections)
  match term with
  | .rigid id => return node ``Term.rigid #[toExpr id]
  | .flexible id => return node ``Term.flexible #[toExpr id]
  | .boolean b => return node ``Term.boolean #[toExpr b]
  | .booleanSet => return node ``Term.booleanSet #[]
  | .logic op left right =>
    return node ``Term.logic #[toExpr op, ← quoteTerm left, ← quoteTerm right]
  | .mem negated element set =>
    return node ``Term.mem #[toExpr negated, ← quoteTerm element, ← quoteTerm set]
  | .enum values => return node ``Term.enum #[← Meta.mkListLit type (← values.mapM quoteTerm)]
  | .functionSet _ site domain range =>
    return node ``Term.functionSet #[enabled, toExpr site, ← quoteTerm domain, ← quoteTerm range]
  | .recordSet _ site fields =>
    let pair := mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) type
    let entries ← fields.mapM fun (name, value) =>
      return mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) type (toExpr name) (← quoteTerm value)
    return node ``Term.recordSet #[enabled, toExpr site, ← Meta.mkListLit pair entries]
  | other => throwError "unexpected expanded ACP_SB term: {reprStr other}"

private def quoteChecked (expression : CheckedExpr noPrimitives .collections) :
    TermElabM Lean.Expr := do
  return mkApp4 (mkConst ``CheckedExpr.mk) (mkConst ``noPrimitives) (mkConst ``Fragment.collections)
    (← quoteTerm expression.term) (← Meta.mkEqRefl (toExpr true))

private def emitSelections : TermElabM Lean.Expr := do
  let checked ← checkedSource
  let initial ← quoteChecked (← select checked "Init" 7)
  let invariant ← quoteChecked (← select checked "TypeInv" 4)
  logInfo "Intact ACP_SB: all 40 units checked, Init and TypeInv selected at state level"
  Meta.mkAppM ``Prod.mk #[initial, invariant]

end

private noncomputable def selections :
    CheckedExpr noPrimitives .collections × CheckedExpr noPrimitives .collections := by_elab
  emitSelections

private abbrev V := Value.{0}
private abbrev Name := ULift.{1} BindingId
private abbrev Scope := DataBridge.scope Name Name
private abbrev Rigid := DataBridge.RigidEnv V Scope
private abbrev State := DataBridge.State V Scope
private abbrev Schema := List (String × SetData.{0})

private def noExternal : ExternalInterpretation V noPrimitives := fun _ _ impossible => nomatch impossible

private meta abbrev participantsId := member 0 0
private meta abbrev yesId := member 0 1
private meta abbrev noId := member 0 2
private meta abbrev undecidedId := member 0 3
private meta abbrev commitId := member 0 4
private meta abbrev abortId := member 0 5
private meta abbrev waitingId := member 0 6
private meta abbrev notsentId := member 0 7
private meta abbrev participantId := member 1 0
private meta abbrev coordinatorId := member 1 1

private def rigidValue (ρ : Rigid) (id : BindingId) : V := ρ PUnit.unit (ULift.up id)
private def stateValue (s : State) (id : BindingId) : V := s PUnit.unit (ULift.up id)

private noncomputable def initialParticipantSchema (ρ : Rigid) : Schema :=
  [("vote", SetData.enum [rigidValue ρ yesId, rigidValue ρ noId]),
   ("alive", SetData.enum [Value.boolean true]),
   ("decision", SetData.enum [rigidValue ρ undecidedId]),
   ("faulty", SetData.enum [Value.boolean false]),
   ("voteSent", SetData.enum [Value.boolean false])]

private def booleanValues : SetData.{0} := SetData.enum [Value.boolean true, Value.boolean false]

private noncomputable def invariantParticipantSchema (ρ : Rigid) : Schema :=
  [("vote", SetData.enum [rigidValue ρ yesId, rigidValue ρ noId]),
   ("alive", booleanValues),
   ("decision", SetData.enum [rigidValue ρ undecidedId, rigidValue ρ commitId, rigidValue ρ abortId]),
   ("faulty", booleanValues),
   ("voteSent", booleanValues)]

private noncomputable def initialCoordinatorSchema (ρ : Rigid) (P : SetData.{0}) : Schema :=
  [("request", P.functionSet (SetData.enum [Value.boolean false])),
   ("vote", P.functionSet (SetData.enum [rigidValue ρ waitingId])),
   ("alive", SetData.enum [Value.boolean true]),
   ("broadcast", P.functionSet (SetData.enum [rigidValue ρ notsentId])),
   ("decision", SetData.enum [rigidValue ρ undecidedId]),
   ("faulty", SetData.enum [Value.boolean false])]

private noncomputable def invariantCoordinatorSchema (ρ : Rigid) (P : SetData.{0}) : Schema :=
  [("request", P.functionSet booleanValues),
   ("vote", P.functionSet (SetData.enum [rigidValue ρ waitingId, rigidValue ρ yesId, rigidValue ρ noId])),
   ("broadcast", P.functionSet (SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ notsentId])),
   ("decision", SetData.enum [rigidValue ρ commitId, rigidValue ρ abortId, rigidValue ρ undecidedId]),
   ("alive", booleanValues),
   ("faulty", booleanValues)]

private noncomputable def predicate (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (selected : CheckedExpr noPrimitives .collections) :
    DataBridge.StatePredicate V Scope :=
  fun ρ s => policy.booleans.holds
    (selected.eval (policy.collectionOperations invalid) policy.booleans noExternal
      ⟨fun id => ρ PUnit.unit (ULift.up id), fun id => s PUnit.unit (ULift.up id)⟩)

private noncomputable def formula (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (selected : CheckedExpr noPrimitives .collections) :
    General.Formula (DataBridge.Carrier V) Scope :=
  .state (.atom (predicate policy invalid selected))

private theorem holds_and_ofProp (B : Booleans V) (p q : Prop) :
    B.holds (Logic.and.eval B (B.ofProp p) (B.ofProp q)) ↔ p ∧ q := by
  have distinct : B.trueValue ≠ B.falseValue := fun eq => B.not_holds_false (eq ▸ B.holds_true)
  by_cases hp : p <;> by_cases hq : q <;>
    simp [Logic.eval, Logic.holds, Booleans.IsBoolean, B.holds_true, B.not_holds_false, distinct, hp, hq]

private theorem init_membership (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (s : State) (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P) :
    predicate policy invalid selections.1 ρ s ↔
      (P.functionSet (SetData.recordSet (initialParticipantSchema ρ))).mem (stateValue s participantId) ∧
      (SetData.recordSet (initialCoordinatorSchema ρ P)).mem (stateValue s coordinatorId) := by
  simp [rigidValue] at domain
  simp [predicate, selections, CheckedExpr.eval, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map, initialParticipantSchema, initialCoordinatorSchema, rigidValue,
    stateValue, domain, holds_and_ofProp]

private theorem typeInv_membership (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (s : State) (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P) :
    predicate policy invalid selections.2 ρ s ↔
      (P.functionSet (SetData.recordSet (invariantParticipantSchema ρ))).mem (stateValue s participantId) ∧
      (SetData.recordSet (invariantCoordinatorSchema ρ P)).mem (stateValue s coordinatorId) := by
  simp [rigidValue] at domain
  simp [predicate, selections, CheckedExpr.eval, Term.eval, Term.evalFields, Term.evalList,
    Operations.collection, Tagged.Policy.collectionOperations, Tagged.Policy.operations,
    Tagged.Policy.booleans, Value.recordSet, Value.checkRecordSetFields,
    Value.decodeRecordSetBounds, Except.map, invariantParticipantSchema, invariantCoordinatorSchema, booleanValues,
    rigidValue, stateValue, domain, holds_and_ofProp]

private def matchesRecord (fields : Schema) (v : V) : Prop :=
  ∃ g, Value.function g = v ∧ g.domain = SetData.recordSetKeys fields ∧ g.fitsRecordSet fields

private def matchesState (P : SetData.{0}) (participantSchema coordinatorSchema : Schema) (s : State) : Prop :=
  (∃ g, Value.function g = stateValue s participantId ∧ g.domain = P ∧
    ∀ k v, g.relates k v → matchesRecord participantSchema v) ∧
  matchesRecord coordinatorSchema (stateValue s coordinatorId)

private theorem matchesState_iff (P : SetData.{0}) (participantSchema coordinatorSchema : Schema) (s : State) :
    matchesState P participantSchema coordinatorSchema s ↔
      (P.functionSet (SetData.recordSet participantSchema)).mem (stateValue s participantId) ∧
      (SetData.recordSet coordinatorSchema).mem (stateValue s coordinatorId) := by
  simp only [matchesState, matchesRecord, SetData.mem_functionSet, SetData.mem_recordSet]

private theorem init_holds_iff (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (σ : Behavior State) (i : Nat) (P : SetData.{0})
    (domain : (rigidValue ρ participantsId).asSet = some P) :
    (formula policy invalid selections.1).Holds ρ σ i ↔
      matchesState P (initialParticipantSchema ρ) (initialCoordinatorSchema ρ P) (σ i) := by
  rw [formula, DataBridge.state_holds, init_membership policy invalid ρ (σ i) P domain,
    matchesState_iff]

private theorem typeInv_holds_iff (policy : Tagged.Policy.{0}) (invalid : Tagged.CollectionPolicy.{0})
    (ρ : Rigid) (σ : Behavior State) (i : Nat) (P : SetData.{0})
    (domain : (rigidValue ρ participantsId).asSet = some P) :
    (formula policy invalid selections.2).Holds ρ σ i ↔
      matchesState P (invariantParticipantSchema ρ) (invariantCoordinatorSchema ρ P) (σ i) := by
  rw [formula, DataBridge.state_holds, typeInv_membership policy invalid ρ (σ i) P domain,
    matchesState_iff]

private theorem enum_mono {xs ys : List V} (sub : ∀ v, v ∈ xs → v ∈ ys) (v : V)
    (h : (SetData.enum xs).mem v) : (SetData.enum ys).mem v :=
  (SetData.mem_enum _ _).mpr (sub v ((SetData.mem_enum _ _).mp h))

private theorem functionSet_mono {D S T : SetData.{0}} (sub : ∀ v, S.mem v → T.mem v) (v : V)
    (h : (D.functionSet S).mem v) : (D.functionSet T).mem v := by
  obtain ⟨g, value, domain, range⟩ := SetData.mem_functionSet.mp h
  exact SetData.mem_functionSet.mpr ⟨g, value, domain, fun x y edge => sub y (range x y edge)⟩

private structure SchemaInclusion (lower upper : Schema) : Prop where
  sameKeys : SetData.recordSetKeys lower = SetData.recordSetKeys upper
  bounds : ∀ name bound, (name, bound) ∈ upper →
    ∃ initial, (name, initial) ∈ lower ∧ ∀ v, initial.mem v → bound.mem v

private theorem SchemaInclusion.matches {lower upper : Schema} (inclusion : SchemaInclusion lower upper)
    {v : V} (h : matchesRecord lower v) : matchesRecord upper v := by
  obtain ⟨g, value, keys, fits⟩ := h
  refine ⟨g, value, keys.trans inclusion.sameKeys, ?_⟩
  intro name bound found
  obtain ⟨initial, member, sub⟩ := inclusion.bounds name bound found
  obtain ⟨field, lookup, proof⟩ := fits name initial member
  exact ⟨field, lookup, sub field proof⟩

private theorem participant_inclusion (ρ : Rigid) :
    SchemaInclusion (initialParticipantSchema ρ) (invariantParticipantSchema ρ) where
  sameKeys := rfl
  bounds := by
    intro name bound h
    simp only [invariantParticipantSchema, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> cases h
    · exact ⟨_, by simp [initialParticipantSchema], fun _ h => h⟩
    · exact ⟨SetData.enum [Value.boolean true], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [rigidValue ρ undecidedId], by simp [initialParticipantSchema], enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialParticipantSchema],
        enum_mono (by simp)⟩

private theorem coordinator_inclusion (ρ : Rigid) (P : SetData.{0}) :
    SchemaInclusion (initialCoordinatorSchema ρ P) (invariantCoordinatorSchema ρ P) where
  sameKeys := by
    apply SetData.ext
    intro key
    simp [SetData.mem_recordSetKeys, initialCoordinatorSchema, invariantCoordinatorSchema,
      or_comm, or_left_comm]
  bounds := by
    intro name bound h
    simp only [invariantCoordinatorSchema, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h <;> cases h
    · exact ⟨P.functionSet (SetData.enum [Value.boolean false]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨P.functionSet (SetData.enum [rigidValue ρ waitingId]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨P.functionSet (SetData.enum [rigidValue ρ notsentId]), by simp [initialCoordinatorSchema],
        functionSet_mono (enum_mono (by simp))⟩
    · exact ⟨SetData.enum [rigidValue ρ undecidedId], by simp [initialCoordinatorSchema], enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean true], by simp [initialCoordinatorSchema],
        enum_mono (by simp)⟩
    · exact ⟨SetData.enum [Value.boolean false], by simp [initialCoordinatorSchema],
        enum_mono (by simp)⟩

/-- Initialization narrows each field range while keeping the exact domains. -/
private theorem init_implies_typeInv (policy : Tagged.Policy.{0})
    (invalid : Tagged.CollectionPolicy.{0}) (ρ : Rigid) (σ : Behavior State) (i : Nat)
    (P : SetData.{0}) (domain : (rigidValue ρ participantsId).asSet = some P)
    (init : (formula policy invalid selections.1).Holds ρ σ i) :
    (formula policy invalid selections.2).Holds ρ σ i := by
  obtain ⟨⟨g, value, keys, fits⟩, coordinator⟩ :=
    (init_holds_iff policy invalid ρ σ i P domain).mp init
  exact (typeInv_holds_iff policy invalid ρ σ i P domain).mpr
    ⟨⟨g, value, keys, fun k v edge => (participant_inclusion ρ).matches (fits k v edge)⟩,
      (coordinator_inclusion ρ P).matches coordinator⟩

#print axioms init_holds_iff
#print axioms typeInv_holds_iff
#print axioms init_implies_typeInv

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.ACP_SB
