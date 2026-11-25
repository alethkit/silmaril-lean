module

import Silmaril.Logic.Temporal.TLA.DataBridge.Thms
import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
public import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Thms
meta import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
meta import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

/-! Source acceptance checks for the intact pinned HourClock and Naturals fixtures. -/

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.HourClock

open Resolution Data.Tagged
open DataElab
open DataElab.Tagged (Policy NumericPrimitive numericSignature)

private meta abbrev clockModule : ModuleId := "HourClock"
private meta abbrev naturalsModule : ModuleId := "Naturals"

private meta abbrev clockSite (path : Path) : Site := ⟨clockModule, path⟩
private meta abbrev hrId : BindingId := .declared (clockSite [.unit 0, .member 0])
private meta abbrev initialId : BindingId := .declared (clockSite [.unit 1])
private meta abbrev nextId : BindingId := .declared (clockSite [.unit 2])
private meta abbrev naturalsId (member : Nat) : BindingId := .declared ⟨naturalsModule, [.member member]⟩
private meta abbrev intervalId : BindingId := naturalsId 0
private meta abbrev additionId : BindingId := naturalsId 1

private meta def numericTable (id : BindingId) : Option NumericPrimitive :=
  if id = intervalId then some .interval
  else if id = additionId then some .add
  else none

private meta abbrev fixtureSignature := numericSignature numericTable

meta section

open Lean

private def externalLevels : Levels.ExternalLevels :=
  let binary : Levels.ExternalSignature := ⟨.constant, [⟨.action, true⟩, ⟨.action, true⟩]⟩
  [(intervalId, binary), (additionId, binary)]

private def naturalsDeclaration (source : Surface.Module) (index : Nat) (symbol : String) :
    Except String SignatureDecl := do
  let some (.definition (.operator .ordinary (.infix _ (.symbol actual) _) _)) :=
    source.units[index]? | throw s!"expected Naturals infix declaration at unit {index}"
  unless actual = symbol do throw s!"expected Naturals {symbol} at unit {index}, got {actual}"
  return .operator (.symbol .infix actual) [.expression, .expression]

private def checkedSource (clockText naturalsText : String) : Except String CheckedRegistry := do
  let clock ← (Surface.Parser.parseModule clockText).mapError
    (fun e => s!"HourClock parse: {reprStr e}")
  let naturals ← (Surface.Parser.parseModule naturalsText).mapError
    (fun e => s!"Naturals parse: {reprStr e}")
  unless clock.name = "HourClock" ∧ clock.extendsModules = ["Naturals"] ∧
      naturals.name = "Naturals" ∧ naturals.extendsModules = [] do
    throw "unexpected fixture module headers or dependencies"
  match clock.units with
  | [.variables ["hr"], .definition (.operator _ (.ident "HCini" []) _),
      .definition (.operator _ (.ident "HCnxt" []) _), .definition (.operator _ (.ident "HC" []) _),
      .theoremDecl ⟨none, .expr _, none⟩] => pure ()
  | _ => throw "unexpected HourClock units"
  let interval ← naturalsDeclaration naturals 11 ".."
  let addition ← naturalsDeclaration naturals 1 "+"
  let registry ← (resolveWith .levelSyntax
    [(clockModule, .parsed clock [("Naturals", naturalsModule)]),
      (naturalsModule, .signature naturals.name [] [interval, addition])] clockModule).mapError
      (fun e => s!"resolution: {reprStr e}")
  let levels ← (Levels.check registry externalLevels).mapError (fun e => s!"levels: {reprStr e}")
  let expected : List (String × Nat × Levels.Level) :=
    [("HCini", 1, .state), ("HCnxt", 2, .action), ("HC", 3, .temporal), ("THEOREM", 4, .temporal)]
  for (name, index, level) in expected do
    let site := clockSite [.unit index, .body]
    unless levels.expressionAt site = some (Levels.LevelTerm.fixed level) do
      throw s!"{name} at {reprStr site}: expected {reprStr level}"
  let some root := registry.moduleAt clockModule | throw "missing resolved HourClock"
  let hourSite := [.unit 1, .body, .operand 0]
  let rangeSite := [.unit 1, .body, .operand 1]
  unless (root.bindingAt (.ident "HCini")).map (·.id) = some initialId ∧
    (root.referenceAt hourSite).map (·.target) = some hrId ∧
    (root.referenceAt rangeSite).map (·.target) = some intervalId do
    throw "unexpected HCini declaration or reference identities"
  let primeSite := [.unit 2, .body, .operand 0]
  let addSite := [.unit 2, .body, .operand 1, .operand 1]
  unless (root.bindingAt (.ident "HCnxt")).map (·.id) = some nextId ∧
    (root.referenceAt primeSite).map (·.target) = some (.builtin (.symbol .postfix "'")) ∧
    (root.referenceAt (primeSite ++ [.operand 0])).map (·.target) = some hrId ∧
    (root.referenceAt addSite).map (·.target) = some additionId ∧
    (root.referenceAt (addSite ++ [.operand 0])).map (·.target) = some hrId do
    throw "unexpected HCnxt declaration or reference identities"
  return registry

private def loadSource : IO CheckedRegistry := do
  let some path ← IO.getEnv "SILMARIL_TLA_HOUR_CLOCK_FIXTURES"
    | throw (IO.userError "stage both fixtures with tla-source-acceptance/check.py")
  let directory := System.FilePath.mk path
  let clockText ← IO.FS.readFile (directory / "HourClock.tla")
  let naturalsText ← IO.FS.readFile (directory / "Naturals.tla")
  match checkedSource clockText naturalsText with
  | .ok registry => return registry
  | .error message => throw (IO.userError message)

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId

/-- Quote the emitted term in the fixture fragment so its semantics can be
checked by the Lean kernel over arbitrary valuations. -/
private partial def quoteTerm (term : DataElab.Term fixtureSignature) :
    Elab.Term.TermElabM Lean.Expr := do
  let signature := mkConst ``fixtureSignature
  let termType := mkApp (mkConst ``DataElab.Term) signature
  let node := fun (ctor : Lean.Name) fields => mkAppN (mkApp (mkConst ctor) signature) fields
  match term with
  | .flexible id => return node ``DataElab.Term.flexible #[toExpr id]
  | .numeral n => return node ``DataElab.Term.numeral #[toExpr n]
  | .prime site operand =>
    return node ``DataElab.Term.prime #[toExpr site, ← quoteTerm operand]
  | .eq negated left right =>
    return node ``DataElab.Term.eq #[toExpr negated, ← quoteTerm left, ← quoteTerm right]
  | .ite condition yes no =>
    return node ``DataElab.Term.ite #[← quoteTerm condition, ← quoteTerm yes, ← quoteTerm no]
  | .mem negated element set =>
    return node ``DataElab.Term.mem #[toExpr negated, ← quoteTerm element, ← quoteTerm set]
  | .external id arity _ args =>
    let key := toExpr id
    let expected ← Meta.mkEq (mkApp signature key) (toExpr (some arity))
    let admitted ← Elab.Term.elabTerm (← `(by
      simp [fixtureSignature, numericSignature, numericTable, intervalId, naturalsId,
        NumericPrimitive.arity])) (some expected)
    let values ← Meta.mkListLit termType (← args.mapM quoteTerm)
    return node ``DataElab.Term.external #[key, toExpr arity, admitted, values]
  | _ => throwError "unexpected term in lowered HCini: {reprStr term}"

private def quoteChecked (constructor : Lean.Name) (term : DataElab.Term fixtureSignature) :
    Elab.Term.TermElabM Lean.Expr := do
  let quoted ← quoteTerm term
  let valid ← Meta.mkEqRefl (toExpr true)
  return mkApp3 (mkConst constructor) (mkConst ``fixtureSignature) quoted valid

private def emitSelections : Elab.Term.TermElabM Lean.Expr := do
  let registry ← loadSource
  let initial ← match Endpoints.lowerState registry externalLevels fixtureSignature 16 initialId with
    | .ok expression => pure expression
    | .error diagnostic => throwError "HCini lowering: {reprStr diagnostic}"
  let next ← match Endpoints.lowerAction registry externalLevels fixtureSignature 16 nextId with
    | .ok action => pure action
    | .error diagnostic => throwError "HCnxt lowering: {reprStr diagnostic}"
  let state ← quoteChecked ``DataElab.CheckedExpr.mk initial.term
  let action ← quoteChecked ``Endpoints.CheckedAction.mk next.term
  logInfo "HourClock levels: HCini state, HCnxt action, HC temporal, anonymous THEOREM temporal"
  Meta.mkAppM ``Prod.mk #[state, action]

end

private noncomputable def checked :
    DataElab.CheckedExpr fixtureSignature × Endpoints.CheckedAction fixtureSignature := by_elab
  emitSelections

private abbrev ClockValue := Value.{0}
private abbrev ClockName := ULift.{1} BindingId
private abbrev ClockScope := DataBridge.scope ClockName ClockName
private abbrev RigidEnv := DataBridge.RigidEnv ClockValue ClockScope
private abbrev ClockState := DataBridge.State ClockValue ClockScope

private noncomputable def hour (s : ClockState) : ClockValue :=
  s PUnit.unit (ULift.up hrId)

private def valuation (ρ : RigidEnv) (s : ClockState) : DataElab.Valuation ClockValue :=
  ⟨fun id => ρ PUnit.unit (ULift.up id), fun id => s PUnit.unit (ULift.up id)⟩

private noncomputable def initial (policy : Policy.{0}) :
    DataBridge.StatePredicate ClockValue ClockScope :=
  fun ρ s => policy.booleans.holds
    (checked.1.eval policy.operations policy.booleans (policy.external numericTable) (valuation ρ s))

private noncomputable def initialFormula (policy : Policy.{0}) :
    General.Formula (DataBridge.Carrier ClockValue) ClockScope :=
  .state (.atom (initial policy))

private theorem intervalSelected : numericTable intervalId = some .interval := by
  simp [numericTable]

/-- State satisfaction comes from the expression selected and lowered from the
intact pinned source. Both valuations and the adapter policy are arbitrary. -/
private theorem hcini_holds_iff (policy : Policy.{0}) (ρ : RigidEnv) (σ : Behavior ClockState)
    (i : Nat) :
    (initialFormula policy).Holds ρ σ i ↔
      ∃ n : Int, hour (σ i) = Value.integer n ∧ 1 ≤ n ∧ n ≤ 12 := by
  rw [initialFormula, DataBridge.state_holds]
  simp only [initial, checked, DataElab.CheckedExpr.eval, DataElab.Term.eval,
    DataElab.Term.evalList, Bool.false_eq_true, ite_false, policy.numeral_eq,
    DataElab.Booleans.holds_ofProp, policy.mem_value, valuation, hour]
  rw [policy.external_apply numericTable intervalSelected]
  simp only [policy.interval_apply, Value.interval_integer, Value.mem_set,
    SetData.mem_intRange, eq_comm, hrId, clockSite]
  rfl

example (policy : Policy.{0}) (ρ : RigidEnv) (σ : Behavior ClockState) (i : Nat)
    (h : hour (σ i) = Value.integer 1) : (initialFormula policy).Holds ρ σ i :=
  (hcini_holds_iff policy ρ σ i).mpr ⟨1, h, by decide, by decide⟩

private theorem additionSelected : numericTable additionId = some .add := by
  simp [numericTable]

private def endpointValuation (ρ : RigidEnv) (s t : ClockState) :
    Endpoints.EndpointValuation ClockValue :=
  let source := valuation ρ s
  ⟨source.rigid, source.flexible, (valuation ρ t).flexible⟩

private noncomputable def next (policy : Policy.{0}) :
    General.Action (DataBridge.Carrier ClockValue) ClockScope :=
  fun ρ s t => policy.booleans.holds
    (checked.2.eval policy.operations policy.booleans (policy.external numericTable)
      (endpointValuation ρ s t))

open Classical in
/-- The primed read uses the target. The IF guard and addition use the source. -/
private theorem hcnxt_iff (policy : Policy.{0}) (ρ : RigidEnv) (s t : ClockState) :
    next policy ρ s t ↔ hour t =
      (if hour s = Value.integer 12 then Value.integer 1
       else Value.add policy.numeric (hour s) (Value.integer 1)) := by
  have guard (p : Prop) : policy.booleans.IsBoolean (policy.booleans.ofProp p) := by
    by_cases h : p <;> simp [DataElab.Booleans.IsBoolean, h]
  simp only [next, checked, Endpoints.CheckedAction.eval, DataElab.Term.eval,
    DataElab.Term.evalList, Bool.false_eq_true, ite_false, ite_true,
    policy.numeral_eq, guard, DataElab.Booleans.holds_ofProp, endpointValuation, valuation, hour]
  rw [policy.external_apply numericTable additionSelected]
  simp only [policy.add_apply, ite_not, hrId, clockSite]
  rfl

open Classical in
private theorem hcnxt_integer_iff (policy : Policy.{0}) (ρ : RigidEnv) (s t : ClockState)
    (n : Int) (source : hour s = Value.integer n) :
    next policy ρ s t ↔ hour t = Value.integer (if n = 12 then 1 else n + 1) := by
  rw [hcnxt_iff, source]
  by_cases h : n = 12 <;> simp [Value.integer_injective.eq_iff, h]

#print axioms hcini_holds_iff
#print axioms hcnxt_iff
#print axioms hcnxt_integer_iff

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.HourClock
