module

public import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Thms
import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Tagged.Thms
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
public import Lean
public meta import Lean

namespace Silmaril.Logic.Temporal.TLA.SourceAcceptance.LiveHourClock

open DataElab DataElab.Temporal Resolution Data.Tagged
open DataElab.Tagged (Policy NumericPrimitive numericSignature)

private meta abbrev hr : BindingId := .declared ⟨"HourClock", [.unit 0, .member 0]⟩
private meta abbrev interval : BindingId := .declared ⟨"Naturals", [.member 0]⟩
private meta abbrev plus : BindingId := .declared ⟨"Naturals", [.member 1]⟩

private meta def numeric (id : BindingId) : Option NumericPrimitive :=
  if id = interval then some .interval else if id = plus then some .add else none

private meta abbrev signature := numericSignature numeric

meta section

open Lean

private def load (dir : System.FilePath) (name : String) : IO Surface.Module := do
  let text ← IO.FS.readFile (dir / (name ++ ".tla"))
  match Surface.Parser.parseModule text with
  | .ok mod =>
    unless mod.name = name do throw (IO.userError s!"unexpected module name {mod.name}")
    return mod
  | .error e => throw (IO.userError s!"{name} parse: {reprStr e}")

private def attestInfix (source : Surface.Module) (index : Nat) (symbol : String) :
    Except String SignatureDecl := do
  let some (.definition (.operator .ordinary (.infix _ (.symbol actual) _) _)) :=
    source.units[index]? | throw s!"expected Naturals infix declaration at unit {index}"
  unless actual = symbol do throw s!"expected Naturals {symbol} at unit {index}"
  return .operator (.symbol .infix actual) [.expression, .expression]

private def checkedForms (live clock naturals tlce : Surface.Module) :
    Except String (Form signature × Form signature × Form signature) := do
  let rangeDecl ← attestInfix naturals 11 ".."
  let plusDecl ← attestInfix naturals 1 "+"
  unless tlce.units.any fun unit =>
      match unit with
      | .definition (.operator .ordinary (.ident "CounterExample" []) _) => true
      | _ => false
    do throw "missing nullary TLCExt.CounterExample"
  let registry ← (resolveWith .levelSyntax
    [("LiveHourClock", .parsed live [("HourClock", "HourClock"), ("TLC", "TLC"), ("TLCExt", "TLCExt")]),
     ("HourClock", .parsed clock [("Naturals", "Naturals")]),
     ("Naturals", .signature "Naturals" [] [rangeDecl, plusDecl]),
     ("TLC", .signature "TLC" [] []),
     ("TLCExt", .signature "TLCExt" [] [.operator (.ident "CounterExample") []])]
    "LiveHourClock").mapError (fun e => s!"resolution: {reprStr e}")
  let binary : Levels.ExternalSignature := ⟨.constant, [⟨.action, true⟩, ⟨.action, true⟩]⟩
  let levels : Levels.ExternalLevels :=
    [(interval, binary), (plus, binary),
      (.declared ⟨"TLCExt", [.member 0]⟩, ⟨.constant, []⟩)]
  let some root := registry.moduleAt "LiveHourClock" | throw "missing resolved root"
  let select := fun name => do
    let some binding := root.bindingAt (.ident name) | throw s!"missing {name}"
    pure (Temporal.lowerFormula registry levels signature 32 binding.id)
  let accept := fun name => do
    let form ← (← select name).mapError (fun e => s!"{name} lowering: {reprStr e}")
    return form.form
  for name in ["AllTimes", "ClockSettles"] do
    let .error (.unsupportedFormula site) ← select name
      | throw s!"expected temporal quantifier rejection for {name}"
    unless site.moduleId = "LiveHourClock" do throw s!"unexpected rejection site for {name}"
  let .error (.data diagnostic) ← select "PostCondition"
    | throw "expected the TLC postcondition to be unsupported"
  unless diagnostic.kind = .missingPrimitive (.declared ⟨"TLCExt", [.member 0]⟩) do
    throw s!"unexpected PostCondition rejection: {reprStr diagnostic}"
  return (← accept "LSpec", ← accept "AlwaysTick", ← accept "TypeInvariance")

deriving instance ToExpr for Resolution.Fixity
deriving instance ToExpr for Resolution.Name
deriving instance ToExpr for Step
deriving instance ToExpr for Site
deriving instance ToExpr for BindingId

/-- Quote the emitted syntax for the fixture so the kernel checks its denotation. -/
private partial def quoteData (term : DataElab.Term signature) : Elab.Term.TermElabM Lean.Expr := do
  let core := fun ctor => mkApp2 (mkConst ctor) (mkConst ``signature) (mkConst ``Fragment.core)
  let node := fun ctor fields => mkAppN (core ctor) fields
  match term with
  | .flexible id => return node ``DataElab.Term.flexible #[toExpr id]
  | .numeral n => return node ``DataElab.Term.numeral #[toExpr n]
  | .prime site operand => return node ``DataElab.Term.prime #[toExpr site, ← quoteData operand]
  | .eq neg l r => return node ``DataElab.Term.eq #[toExpr neg, ← quoteData l, ← quoteData r]
  | .mem neg x s => return node ``DataElab.Term.mem #[toExpr neg, ← quoteData x, ← quoteData s]
  | .ite c y n => return node ``DataElab.Term.ite #[← quoteData c, ← quoteData y, ← quoteData n]
  | .external id arity _ args =>
    let key := toExpr id
    let expected ← Meta.mkEq (mkApp (mkConst ``signature) key) (toExpr (some arity))
    let admitted ← Elab.Term.elabTerm (← `(by
      simp [signature, numericSignature, numeric, interval, plus, NumericPrimitive.arity])) (some expected)
    let values ← Meta.mkListLit (core ``DataElab.Term) (← args.mapM quoteData)
    return node ``DataElab.Term.external #[key, toExpr arity, admitted, values]
  | _ => throwError "unexpected clock data term: {reprStr term}"

private def quoteChecked (e : CheckedExpr signature) : Elab.Term.TermElabM Lean.Expr := do
  Meta.mkAppM ``DataElab.CheckedExpr.mk #[← quoteData e.term, ← Meta.mkEqRefl (toExpr true)]

private def quotePred : Predicate signature → Elab.Term.TermElabM Lean.Expr
  | .data e => do Meta.mkAppM ``Predicate.data #[← quoteChecked e]
  | _ => throwError "expected a data predicate leaf"

private def quoteObs (obs : Observation signature) : Elab.Term.TermElabM Lean.Expr := do
  let type := mkApp2 (mkConst ``DataElab.CheckedExpr) (mkConst ``signature) (mkConst ``Fragment.core)
  Meta.mkListLit type (← obs.mapM quoteChecked)

private def quoteForm : Form signature → Elab.Term.TermElabM Lean.Expr
  | .state p => do Meta.mkAppM ``Form.state #[← quotePred p]
  | .binary .and p q => do
    Meta.mkAppM ``Form.binary #[mkConst ``Logic.and, ← quoteForm p, ← quoteForm q]
  | .always p => do Meta.mkAppM ``Form.always #[← quoteForm p]
  | .alwaysBracket p obs => do Meta.mkAppM ``Form.alwaysBracket #[← quotePred p, ← quoteObs obs]
  | .eventuallyAngle p obs => do Meta.mkAppM ``Form.eventuallyAngle #[← quotePred p, ← quoteObs obs]
  | .fairness .weak p obs => do
    Meta.mkAppM ``Form.fairness #[mkConst ``Surface.Fairness.weak, ← quotePred p, ← quoteObs obs]
  | _ => throwError "unexpected temporal clock form"

private def emitForms : Elab.Term.TermElabM Lean.Expr := do
  let some path ← IO.getEnv "SILMARIL_TLA_LIVE_CLOCK_FIXTURES"
    | throwError "stage the clock fixtures with tla-temporal-source/check.py"
  let dir := System.FilePath.mk path
  let forms := checkedForms (← load dir "LiveHourClock") (← load dir "HourClock")
    (← load dir "Naturals") (← load dir "TLCExt")
  let (spec, tick, inv) ← match forms with
    | .ok result => pure result
    | .error message => throwError "{message}"
  let properties ← Meta.mkAppM ``Prod.mk #[← quoteForm tick, ← quoteForm inv]
  Meta.mkAppM ``Prod.mk #[← quoteForm spec, properties]

end

private noncomputable def selected : Form signature × Form signature × Form signature := by_elab emitForms

private abbrev ClockValue := Value.{0}
private abbrev ClockState := State ClockValue

private noncomputable def interp (policy : Policy.{0}) : Interpretation ClockValue signature :=
  ⟨policy.operations, policy.booleans, policy.external numeric⟩

private noncomputable def initial (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    StatePred ClockState :=
  match selected.2.2 with
  | .always (.state p) => p.toStatePred I ρ
  | _ => fun _ => False

private noncomputable def next (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    Action ClockState :=
  match selected.2.1 with
  | .always (.eventuallyAngle p _) => p.toAction I ρ
  | _ => fun _ _ => False

private noncomputable def hour (s : ClockState) : ClockValue := s hr
private noncomputable def observedHour (s : ClockState) : List ClockValue := [hour s]

private theorem initial_iff (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s : ClockState) :
    initial (interp policy) ρ s ↔ ∃ n : Int, hour s = Value.integer n ∧ 1 ≤ n ∧ n ≤ 12 := by
  simp only [initial, selected, interp, Predicate.toStatePred, Predicate.toAction, Predicate.eval,
    DataElab.Term.eval, DataElab.Term.evalList, Bool.false_eq_true, ite_false,
    Booleans.holds_ofProp, policy.numeral_eq, policy.mem_value, hour]
  rw [policy.external_apply numeric (show numeric interval = some .interval by simp [numeric])]
  simp only [policy.interval_apply, Value.interval_integer, Value.mem_set, SetData.mem_intRange, eq_comm]
  rfl

open Classical in
private theorem next_integer_iff (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s t : ClockState)
    (n : Int) (h : hour s = Value.integer n) :
    next (interp policy) ρ s t ↔ hour t = Value.integer (if n = 12 then 1 else n + 1) := by
  have guard (p : Prop) : policy.booleans.IsBoolean (policy.booleans.ofProp p) := by
    by_cases hp : p <;> simp [Booleans.IsBoolean, hp]
  simp only [next, selected, interp, Predicate.toAction, Predicate.eval, DataElab.Term.eval,
    DataElab.Term.evalList, Bool.false_eq_true, ite_false, ite_true,
    policy.numeral_eq, guard, Booleans.holds_ofProp, hour] at *
  rw [policy.external_apply numeric (show numeric plus = some .add by simp [numeric, interval, plus]), h]
  by_cases hn : n = 12 <;> simp [hn, policy.add_apply, Value.integer_injective.eq_iff]

private theorem spec_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.1.toFormula I ρ =
      .conj (.conj (.state (initial I ρ)) (.alwaysBracket (next I ρ) observedHour))
        (.weakFair (next I ρ) observedHour) := rfl

private theorem tick_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.2.1.toFormula I ρ = .always (.eventuallyAngle (next I ρ) observedHour) := rfl

private theorem invariant_shape (I : Interpretation ClockValue signature) (ρ : RigidEnv ClockValue) :
    selected.2.2.toFormula I ρ = .always (.state (initial I ρ)) := rfl

private theorem preserves (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s t : ClockState)
    (hs : initial (interp policy) ρ s) (hst : Action.bracket (next (interp policy) ρ) observedHour s t) :
    initial (interp policy) ρ t := by
  obtain ⟨n, hn, hlo, hhi⟩ := (initial_iff policy ρ s).mp hs
  apply (initial_iff policy ρ t).mpr
  rcases hst with step | idle
  · have ht := (next_integer_iff policy ρ s t n hn).mp step
    refine ⟨_, ht, ?_, ?_⟩ <;> split <;> omega
  · have ht : hour t = hour s := (List.singleton_inj.mp idle)
    exact ⟨n, ht.trans hn, hlo, hhi⟩

private theorem tick_enabled (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (s : ClockState)
    (hs : initial (interp policy) ρ s) : ((next (interp policy) ρ).angle observedHour).enabled s := by
  obtain ⟨n, hn, _, _⟩ := (initial_iff policy ρ s).mp hs
  let m := if n = 12 then 1 else n + 1
  let t : ClockState := fun id => if id = hr then Value.integer m else s id
  have ht : hour t = Value.integer m := by simp [hour, t]
  refine ⟨t, (next_integer_iff policy ρ s t n hn).mpr ht, ?_⟩
  intro h
  have eq := Value.integer_injective (ht.symm.trans ((List.singleton_inj.mp h).trans hn))
  dsimp [m] at eq
  split at eq <;> omega

/-- The intact LSpec entails recurrent changing ticks and type invariance for
arbitrary tagged valuations and every fixed adapter policy. -/
private theorem live_hour_clock (policy : Policy.{0}) (ρ : RigidEnv ClockValue) (σ : Behavior ClockState)
    (h : (selected.1.toFormula (interp policy) ρ).Sat σ) :
    (selected.2.1.toFormula (interp policy) ρ).Sat σ ∧
    (selected.2.2.toFormula (interp policy) ρ).Sat σ := by
  rw [spec_shape] at h
  have hInit : initial (interp policy) ρ (σ 0) := h.1.1
  have step : ∀ i, (next (interp policy) ρ).bracket observedHour (σ i) (σ (i + 1)) :=
    fun i => h.1.2 i (Nat.zero_le i)
  have invariant (i : Nat) : initial (interp policy) ρ (σ i) := by
    induction i with
    | zero => exact hInit
    | succ i ih => exact preserves policy ρ _ _ ih (step i)
  have recurring := (Formula.holds_weakFair _ _ σ 0).mp h.2
    ⟨0, Nat.le_refl _, fun j _ => tick_enabled policy ρ _ (invariant j)⟩
  rw [tick_shape, invariant_shape]
  refine ⟨?_, fun i _ => invariant i⟩
  intro i hi
  exact (Formula.holds_eventuallyAngle _ _ σ i).mpr (recurring i hi)

#print axioms live_hour_clock

end Silmaril.Logic.Temporal.TLA.SourceAcceptance.LiveHourClock
