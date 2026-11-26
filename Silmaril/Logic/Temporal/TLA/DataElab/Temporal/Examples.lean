module

meta import Silmaril.Logic.Temporal.TLA.DataElab.Temporal.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Source admission and rejection cases for the temporal data bridge. -/

namespace Silmaril.Logic.Temporal.TLA.DataElab.Temporal

open Resolution

private meta def registry (text : String) : Except String CheckedRegistry := do
  let source ← (Surface.Parser.parseModule text).mapError reprStr
  (resolveWith .levelSyntax [("root", .parsed source [])] "root").mapError reprStr

private meta def id (index : Nat) : BindingId := .declared ⟨"root", [.unit index]⟩
private meta def signature : ExternalSignature := fun _ => none

private meta def accepted : String := r"
---- MODULE Actions ----
VARIABLES x, y
Next == x' = y
Square == [Next]_<<x, y>>
Angle == <<Next>>_(IF x = 0 THEN y ELSE x)
Idle == UNCHANGED <<x, y>>
CanMove == ENABLED (Angle /\ ~Idle)
Spec == /\ CanMove
        /\ [][Next]_x
        /\ SF_x(Next)
Goal == (<>CanMove ~> []CanMove) <=> ~(<>FALSE \/ []FALSE)
====
"

private meta def acceptedShapes : Except String Bool := do
  let checked ← registry accepted
  let step := fun index => lowerAction checked [] signature 32 (id index)
  let .ok square := step 2 | throw "square action"
  let .ok angle := step 3 | throw "angle action"
  let .ok idle := step 4 | throw "unchanged action"
  let .ok enabled := lowerState checked [] signature 32 (id 5) | throw "enabled state predicate"
  let .ok spec := lowerFormula checked [] signature 32 (id 6) | throw "specification"
  let .ok goal := lowerFormula checked [] signature 32 (id 7) | throw "temporal Boolean formula"
  let .error (.bareAction _) := lowerFormula checked [] signature 32 (id 1)
    | throw "raw action promoted to formula"
  let .error (.wrongLevel _ .state .action) := lowerState checked [] signature 32 (id 2)
    | throw "square action selected as state predicate"
  match square.predicate, angle.predicate, idle.predicate, enabled.predicate, spec.form, goal.form with
  | .bracket .square (.data _) [_, _], .bracket .angle (.data _) [_], .unchanged [_, _],
    .enabled (.binary .and (.bracket .angle _ _) (.neg (.unchanged _))),
    .junction .conjunction [.state _, .alwaysBracket _ _, .fairness .strong _ _],
    .binary .equiv (.leadsTo (.eventually _) (.always _))
      (.neg (.binary .or (.eventually _) (.always _))) => return true
  | _, _, _, _, _, _ => throw "unexpected temporal lowering shape"

#guard match acceptedShapes with | .ok true => true | _ => false

private meta def badOperand (body : String) : Bool :=
  let text := "---- MODULE Bad ----\nVARIABLE x\nNext == x' = x\nF == " ++ body ++ "\n===="
  match registry text with
  | .ok checked =>
    match lowerFormula checked [] signature 32 (id 2) with
    | .error (.levels _) => true
    | _ => false
  | .error _ => false

#guard badOperand "[]Next"
#guard badOperand "<>[Next]_x"
#guard badOperand "[]<<Next>>_x"
#guard badOperand "ENABLED ([]TRUE)"
#guard badOperand "UNCHANGED (x')"
#guard badOperand "[][Next]_(x')"
#guard badOperand "WF_x([]TRUE)"
#guard badOperand "Next /\\ []TRUE"
#guard badOperand "Next ~> TRUE"

-- A noncontributing primitive slot may accept an action operand. Retaining
-- that prime in a state observation would read the wrong endpoint.
private meta def rejectsRetainedPrime : Bool := Id.run do
  let text := "---- MODULE BadObservation ----\nEXTENDS Lib\nVARIABLE x\nF == UNCHANGED Drop(x')\n===="
  let .ok source := Surface.Parser.parseModule text | return false
  let .ok checked := resolveWith .levelSyntax [
    ("root", .parsed source [("Lib", "lib")]),
    ("lib", .signature "Lib" [] [.operator (.ident "Drop") [.expression]])] "root" | return false
  let drop : BindingId := .declared ⟨"lib", [.member 0]⟩
  let levels : Levels.ExternalLevels := [(drop, ⟨.constant, [⟨.action, false⟩]⟩)]
  let admits : ExternalSignature := fun binding => if binding = drop then some 1 else none
  let .error (.primeInState site) := lowerAction checked levels admits 32 (id 1) | return false
  return site = ⟨"root", [.unit 1, .body, .operand 0, .argument 0]⟩

#guard rejectsRetainedPrime

private meta def rejectsTemporalPrimitive : Bool := Id.run do
  let text := "---- MODULE BadPrimitive ----\nEXTENDS Lib\nF == Drop(Future)\n===="
  let .ok source := Surface.Parser.parseModule text | return false
  let .ok checked := resolveWith .levelSyntax [
    ("root", .parsed source [("Lib", "lib")]),
    ("lib", .signature "Lib" [] [
      .operator (.ident "Drop") [.expression], .operator (.ident "Future") []])] "root" | return false
  let drop : BindingId := .declared ⟨"lib", [.member 0]⟩
  let future : BindingId := .declared ⟨"lib", [.member 1]⟩
  let levels : Levels.ExternalLevels :=
    [(drop, ⟨.constant, [⟨.temporal, false⟩]⟩), (future, ⟨.temporal, []⟩)]
  let admits : ExternalSignature := fun binding =>
    if binding = drop then some 1 else if binding = future then some 0 else none
  let .error (.temporalPrimitive binding) := lowerState checked levels admits 32 (id 0)
    | return false
  return binding = future

#guard rejectsTemporalPrimitive

end Silmaril.Logic.Temporal.TLA.DataElab.Temporal
