module

import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Defs
import all Silmaril.Logic.Temporal.TLA.DataElab.Endpoints.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
import Lean
meta import Lean

/-! Parsed replay regressions and kernel-checked state and endpoint equations. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Instances.Examples

open Resolution

private structure Fixture where
  id : ModuleId
  name : String
  units : String
  imports : ImportMap := []

private meta def inputs (fixtures : List Fixture) : Except String Registry :=
  fixtures.mapM fun fixture => do
    let source ← (Surface.Parser.parseModule
      s!"---- MODULE {fixture.name} ----\n{fixture.units}\n====\n").mapError reprStr
    return (fixture.id, .parsed source fixture.imports)

private meta def verify (fixtures : List Fixture) : Except String Resolution.Instances.CheckedInstances := do
  (Resolution.Instances.check (← inputs fixtures) "root").mapError reprStr

private meta def bindingAtRoot (checked : Resolution.Instances.CheckedInstances) (name : String) :
    Except String BindingId := do
  let some binding := (checked.registry.moduleAt "root").bind (·.bindingAt (.ident name))
    | throw s!"No such root binding {name}"
  return binding.id

private meta def signature : ExternalSignature := fun _ => none

-- The first five action definitions and their models come from the replay probe.
private meta def nested : List Fixture := [
  ⟨"leaf", "Leaf",
    "VARIABLE cell\nLOCAL Read == cell\nSample(a) == (Read' # a) /\\ (Read = a')\nCurrent == Read", []⟩,
  ⟨"mid", "Middle",
    "VARIABLE bridge\nInner(b) == INSTANCE Leaf WITH cell <- bridge # b\n\
     Through(k) == Inner(TRUE)!Sample(k)", [("Leaf", "leaf")]⟩,
  ⟨"constant", "Constants", "CONSTANT C\nExpose == C", []⟩,
  ⟨"root", "Root",
    "VARIABLE x, y, z\nI(p) == INSTANCE Middle WITH bridge <- p /\\ x\n\
     J(p) == INSTANCE Middle WITH bridge <- p \\/ x\n\
     DirectI == I(y)!Inner(z)!Sample(x # z)\n\
     DirectJ == J(y)!Inner(z)!Sample(x # z)\n\
     HomeCall == I(y)!Through(x # z)\n\
     ActionRhs == INSTANCE Constants WITH C <- x'\nExplicitShift == ActionRhs!Expose\n\
     Relay == INSTANCE Leaf WITH cell <- I(y)!Inner(z)!Current\nPriorCall == Relay!Sample(x # z)\n\
     Before == I(y)!Inner(z)!Current\nAfter == Before'\nRepeated == {DirectI, DirectJ}",
    [("Middle", "mid"), ("Constants", "constant"), ("Leaf", "leaf")]⟩]

private meta def nestedShared : List Fixture := [
  ⟨"common", "Common", "VARIABLE signal", []⟩,
  ⟨"leaf", "Leaf", "EXTENDS Common\nLOCAL Read == signal\nPeek == Read'",
    [("Common", "common")]⟩,
  ⟨"mid", "Middle", "EXTENDS Common\nInner == INSTANCE Leaf\nThrough == Inner!Peek",
    [("Common", "common"), ("Leaf", "leaf")]⟩,
  ⟨"root", "Root",
    "EXTENDS Common\nOuter == INSTANCE Middle WITH signal <- ~signal\n\
     Direct == Outer!Inner!Peek\nIndirect == Outer!Through",
    [("Common", "common"), ("Middle", "mid")]⟩]

private meta def swap : List Fixture := [
  ⟨"common", "Common", "VARIABLE x, y", []⟩,
  ⟨"leaf", "Leaf", "EXTENDS Common\nLOCAL Read == {x, {y}}\nOut == Read",
    [("Common", "common")]⟩,
  ⟨"root", "Root",
    "EXTENDS Common\nI == INSTANCE Leaf WITH x <- y, y <- x\n\
     J == INSTANCE Leaf WITH x <- y\nSwap == I!Out\nImplicit == J!Out",
    [("Common", "common"), ("Leaf", "leaf")]⟩]

#guard match verify nested with
  | .ok checked => match bindingAtRoot checked "Before", bindingAtRoot checked "After" with
    | .ok before, .ok after =>
      (lowerState checked signature 96 before).isOk && (lowerAction checked signature 96 after).isOk &&
        match lowerDefinition checked.registry signature 96 before with
        | .error diagnostic => diagnostic.kind = .unsupported .proofOrQualifiedReference
        | .ok _ => false
    | _, _ => false
  | .error _ => false

#guard match verify nested with
  | .ok checked => match bindingAtRoot checked "After" with
    | .ok after => match lowerAction checked signature 3 after with
      | .error (.lowering diagnostic) => diagnostic.kind = .expansionLimit
      | _ => false
    | .error _ => false
  | .error _ => false

#guard match inputs [
    ⟨"leaf", "Leaf", "CONSTANT F(_)\nOut == F(TRUE)", []⟩,
    ⟨"root", "Root", "INSTANCE Leaf WITH F <- TRUE", [("Leaf", "leaf")]⟩] with
  | .ok registry => match Resolution.Instances.check registry "root" with
    | .error (.resolution diagnostic) => diagnostic =
        ⟨⟨"root", [.unit 0, .substitution 0]⟩, .unsupported .operatorSubstitution⟩
    | _ => false
  | .error _ => false

private meta def exceedsCap (call : String) (owner : ModuleId) : Bool :=
  match inputs (nested.map fun fixture =>
    if fixture.id = "root" then { fixture with units := fixture.units ++ "\nBad == " ++ call }
    else fixture) with
  | .ok registry => match Resolution.Instances.check registry "root" with
    | .error (.levels ⟨site, .failedRequirement requirement⟩) =>
      site = ⟨"root", [.unit 13, .body]⟩ ∧ requirement.origin.moduleId = owner ∧
        requirement.condition = .atMost (.fixed .action) .state
    | _ => false
  | .error _ => false

#guard exceedsCap "I(y')!Inner(z)!Sample(x # z)" "root"
#guard exceedsCap "I(y)!Inner(z')!Sample(x # z)" "mid"
#guard exceedsCap "I(y)!Inner(z)!Sample((x # z)')" "leaf"

open Lean in
private meta def quoteSite (site : Site) : Elab.Term.TermElabM Lean.Expr := do
  let steps ← site.path.mapM fun step => match step with
    | .unit i => pure (mkApp (mkConst ``Step.unit) (toExpr i))
    | .member i => pure (mkApp (mkConst ``Step.member) (toExpr i))
    | .operand i => pure (mkApp (mkConst ``Step.operand) (toExpr i))
    | .substitution i => pure (mkApp (mkConst ``Step.substitution) (toExpr i))
    | .body => pure (mkConst ``Step.body)
    | _ => throwError "unexpected site step: {reprStr step}"
  return mkApp2 (mkConst ``Site.mk) (toExpr site.moduleId) (← Meta.mkListLit (mkConst ``Step) steps)

open Lean in
-- This quotation only covers the constructors used in the fixtures.
private meta partial def quoteTerm (term : Term signature) : Elab.Term.TermElabM Lean.Expr := do
  let sig := mkConst ``signature
  let init := fun (ctor : Lean.Name) => mkApp2 (mkConst ctor) sig (mkConst ``Fragment.core)
  let node := fun (ctor : Lean.Name) args => mkAppN (init ctor) args
  match term with
  | .flexible (.declared site) =>
    return node ``Term.flexible #[mkApp (mkConst ``BindingId.declared) (← quoteSite site)]
  | .boolean value => return node ``Term.boolean #[toExpr value]
  | .eq negated left right => return node ``Term.eq #[toExpr negated, ← quoteTerm left, ← quoteTerm right]
  | .logic .and left right =>
    return node ``Term.logic #[mkConst ``Logic.and, ← quoteTerm left, ← quoteTerm right]
  | .logic .or left right =>
    return node ``Term.logic #[mkConst ``Logic.or, ← quoteTerm left, ← quoteTerm right]
  | .not arg => return node ``Term.not #[← quoteTerm arg]
  | .prime site arg => return node ``Term.prime #[← quoteSite site, ← quoteTerm arg]
  | .enum args =>
    let items ← args.mapM quoteTerm
    return node ``Term.enum #[← Meta.mkListLit (init ``Term) items]
  | _ => throwError "unexpected fixture term: {reprStr term}"

open Lean in
private meta def emit (fixtures : List Fixture) (name : String) (action : Bool) :
    Elab.Term.TermElabM Lean.Expr := do
  let expand : Except String (Term signature) := do
    let checked ← verify fixtures
    let id ← bindingAtRoot checked name
    if action then
      return (← (lowerAction checked signature 96 id).mapError reprStr).term
    else
      return (← (lowerState checked signature 96 id).mapError reprStr).term
  let term ← match expand with
    | .ok term => quoteTerm term
    | .error diagnostic => throwError "{diagnostic}"
  let valid ← Meta.mkEqRefl (toExpr true)
  let sig := mkConst ``signature
  return if action then mkApp3 (mkConst ``Endpoints.CheckedAction.mk) sig term valid
    else mkApp4 (mkConst ``CheckedExpr.mk) sig (mkConst ``Fragment.core) term valid

private noncomputable def directI : Endpoints.CheckedAction signature := by_elab emit nested "DirectI" true
private noncomputable def directJ : Endpoints.CheckedAction signature := by_elab emit nested "DirectJ" true
private noncomputable def homeCall : Endpoints.CheckedAction signature := by_elab emit nested "HomeCall" true
private noncomputable def explicitShift : Endpoints.CheckedAction signature :=
  by_elab emit nested "ExplicitShift" true
private noncomputable def priorCall : Endpoints.CheckedAction signature :=
  by_elab emit nested "PriorCall" true
private noncomputable def before : CheckedExpr signature := by_elab emit nested "Before" false
private noncomputable def after : Endpoints.CheckedAction signature := by_elab emit nested "After" true
private noncomputable def repeated : Endpoints.CheckedAction signature :=
  by_elab emit nested "Repeated" true
private noncomputable def direct : Endpoints.CheckedAction signature :=
  by_elab emit nestedShared "Direct" true
private noncomputable def indirect : Endpoints.CheckedAction signature :=
  by_elab emit nestedShared "Indirect" true
private noncomputable def swapped : CheckedExpr signature := by_elab emit swap "Swap" false
private noncomputable def implicitValue : CheckedExpr signature := by_elab emit swap "Implicit" false

private def boolModel : Booleans Bool where
  trueValue := true
  falseValue := false
  holds := (· = true)
  holds_true := rfl
  not_holds_false := Bool.false_ne_true
  invalid := fun _ _ => false

@[simp] private theorem boolTrue : boolModel.trueValue = true := rfl

@[simp] private theorem boolEq (a b : Bool) : boolModel.ofProp (a = b) = (a == b) := by
  cases a <;> cases b <;> simp [boolModel, Booleans.ofProp]

@[simp] private theorem boolNe (a b : Bool) : boolModel.ofProp (a ≠ b) = (a != b) := by
  cases a <;> cases b <;> simp [boolModel, Booleans.ofProp]

@[simp] private theorem boolValid (a : Bool) : boolModel.IsBoolean a := by
  cases a <;> simp [boolModel, Booleans.IsBoolean]

@[simp] private theorem boolNot (a : Bool) : boolModel.ofProp (¬ boolModel.holds a) = !a := by
  cases a <;> simp [boolModel, Booleans.ofProp]

@[simp] private theorem boolAnd (a b : Bool) : Logic.eval .and boolModel a b = (a && b) := by
  cases a <;> cases b <;> simp [Logic.eval, Logic.holds, boolModel, Booleans.IsBoolean, Booleans.ofProp]

@[simp] private theorem boolOr (a b : Bool) : Logic.eval .or boolModel a b = (a || b) := by
  cases a <;> cases b <;> simp [Logic.eval, Logic.holds, boolModel, Booleans.IsBoolean, Booleans.ofProp]

universe u
private def noExternal {V : Type u} : ExternalInterpretation V signature :=
  fun _ _ admitted => nomatch admitted

private def read (x y z : Bool) (id : BindingId) : Bool :=
  if id = .declared ⟨"root", [.unit 0, .member 0]⟩ then x
  else if id = .declared ⟨"root", [.unit 0, .member 1]⟩ then y
  else z

private noncomputable def observe (ops : DataOperations Bool) (action : Endpoints.CheckedAction signature)
    (source target : BindingId → Bool) : Bool :=
  action.eval ops boolModel noExternal ⟨fun _ => false, source, target⟩

private def expected (sx sz tx tz sourceCell targetCell : Bool) :=
  (targetCell != (sx != sz)) && (sourceCell == (tx != tz))

private theorem nested_eq (ops : DataOperations Bool) (sx sy sz tx ty tz : Bool) :
    observe ops directI (read sx sy sz) (read tx ty tz) =
      expected sx sz tx tz ((sy && sx) != sz) ((ty && tx) != tz) ∧
    observe ops directJ (read sx sy sz) (read tx ty tz) =
      expected sx sz tx tz ((sy || sx) != sz) ((ty || tx) != tz) ∧
    observe ops homeCall (read sx sy sz) (read tx ty tz) =
      expected sx sz tx tz (!(sy && sx)) (!(ty && tx)) ∧
    observe ops explicitShift (read sx sy sz) (read tx ty tz) = tx ∧
    observe ops priorCall (read sx sy sz) (read tx ty tz) =
      expected sx sz tx tz ((sy && sx) != sz) ((ty && tx) != tz) := by
  simp [observe, Endpoints.CheckedAction.eval, Term.eval, directI, directJ, homeCall,
    explicitShift, priorCall, read, expected]
  cases sx <;> cases sy <;> cases tx <;> cases ty <;> simp [boolModel, Booleans.ofProp]

private theorem repeated_eq (ops : DataOperations Bool) (source target : BindingId → Bool) :
    observe ops repeated source target =
      ops.enum [observe ops directI source target, observe ops directJ source target] := rfl

private theorem host_endpoints_eq (ops : DataOperations Bool) (sx sy sz tx ty tz : Bool) :
    before.eval ops boolModel noExternal ⟨fun _ => false, read sx sy sz⟩ = ((sy && sx) != sz) ∧
    observe ops after (read sx sy sz) (read tx ty tz) = ((ty && tx) != tz) := by
  simp [observe, Endpoints.CheckedAction.eval, CheckedExpr.eval, Term.eval, before, after, read]

private theorem shared_id_eq (ops : DataOperations Bool) (source target : Bool) :
    observe ops direct (fun _ => source) (fun _ => target) = !target ∧
    observe ops indirect (fun _ => source) (fun _ => target) = !target := by
  simp [observe, Endpoints.CheckedAction.eval, Term.eval, direct, indirect]

private def inherited (idx : Nat) : BindingId := .declared ⟨"common", [.unit 0, .member idx]⟩

private theorem simultaneous_eq {V : Type u} (ops : DataOperations V) (B : Booleans V) (v : Valuation V) :
    swapped.eval ops B noExternal v =
      ops.enum [v.flexible (inherited 1), ops.enum [v.flexible (inherited 0)]] ∧
    implicitValue.eval ops B noExternal v =
      ops.enum [v.flexible (inherited 1), ops.enum [v.flexible (inherited 1)]] :=
  ⟨rfl, rfl⟩

end Silmaril.Logic.Temporal.TLA.DataElab.Instances.Examples
