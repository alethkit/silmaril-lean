module

import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Level checks exercising the native parser and the binding graph. -/

namespace Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples

open Surface

private def site (path : Path) : Site := ⟨"root", path⟩
private def declared (path : Path) : BindingId := .declared (site path)

private def parse (name body : String) : Option Surface.Module :=
  (Parser.parseModule s!"---- MODULE {name} ----\n{body}\n====\n").toOption

private def resolveText (body : String) : Option CheckedRegistry := do
  let source ← parse "Root" body
  (resolveWith .levelSyntax [("root", .parsed source [])] "root").toOption

private def checkText (body : String) : Option (Except Diagnostic CheckedLevels) :=
  (resolveText body).map fun registry => check registry

private def reject (body : String) (path : Path) (kind : DiagnosticKind) : Bool :=
  match checkText body with
  | some (.error error) => error = ⟨site path, kind⟩
  | _ => false

private def failsAt (body : String) (path origin : Path) (condition : Condition) : Bool :=
  reject body path (.failedRequirement ⟨site origin, condition⟩)

private def bodyHas (checked : CheckedLevels) (unit : Nat) (level : Level) : Bool :=
  checked.expressionAt (site [.unit unit, .body]) = some (.fixed level)

private def propagation : Bool := Id.run do
  let some (.ok result) := checkText
    "CONSTANT c, Decl(_)\nVARIABLE v\nIdentity(a) == a\nIgnore(b) == TRUE\n\
     Primed(k) == k'\nByAlias(z) == Primed(Identity(z))\nConstantPrime == c'\n\
     ActionIdentity == Identity(v')\nConstantIgnored == Ignore(v')\n\
     DeclaredAction == Decl(v')\nDeclaredTemporal == Decl([]v)\nTemporalIgnored == Ignore([]v)"
    | return false
  let some alias := result.operatorAt (declared [.unit 5]) | return false
  let some identity := result.operatorAt (declared [.unit 2]) | return false
  let some ignore := result.operatorAt (declared [.unit 3]) | return false
  return decide (identity.result = .parameter (declared [.unit 2, .parameter 0])) &&
    decide (ignore.result = .fixed .constant) &&
    decide (alias.result = .fixed .action) &&
    decide (alias.maxArgumentLevels = [.state]) &&
    decide (identity.maxArgumentLevels = [.temporal]) &&
    bodyHas result 6 .action && bodyHas result 7 .action && bodyHas result 8 .constant &&
    bodyHas result 9 .action && bodyHas result 10 .temporal && bodyHas result 11 .constant

#guard propagation

private def rigidAndLet : Bool := Id.run do
  let some (.ok result) := checkText
    "VARIABLE v\nQ == \\A x \\in {v}: x = x\nR == \\A y: y' = y\n\
     F(p) == LET Local(q) == p /\\ q IN Local(TRUE)\n\
     G(r) == LET Checked(s) == r' IN TRUE\nGood == G(v)\nA == F(v')\n\
     B == LET Unused == v' IN TRUE\nC == {x : x \\in {v}}"
    | return false
  let some localSummary := result.operatorAt (declared [.unit 3, .body, .letDecl 0]) | return false
  let some g := result.operatorAt (declared [.unit 4]) | return false
  let scope := [.unit 3, .body, .letDecl 0]
  return bodyHas result 1 .state && bodyHas result 2 .action &&
    bodyHas result 5 .constant && bodyHas result 6 .action &&
    bodyHas result 7 .constant && bodyHas result 8 .state &&
    decide (localSummary.result.dependencies =
      [declared [.unit 3, .parameter 0], declared (scope ++ [.parameter 0])]) &&
    decide (g.result = .fixed .constant) &&
    decide (g.maxArgumentLevels = [.state]) &&
    (result.expressionAt (site [.unit 1, .body, .body, .operand 0]) = some (.fixed .constant))

#guard rigidAndLet

#guard failsAt "VARIABLE v\nA == (v')'" [.unit 1, .body, .operand 0] [.unit 1, .body, .operand 0]
  (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nA == v'\nB == A'" [.unit 2, .body, .operand 0] [.unit 2, .body, .operand 0]
  (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nP(t) == t'\nB == P(v')" [.unit 2, .body] [.unit 1, .body, .operand 0]
  (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nP(t) == t'\nIgnore(d) == TRUE\nF(x) == Ignore(P(x))\nB == F(v')"
  [.unit 4, .body] [.unit 1, .body, .operand 0] (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nF(x) == LET P(y) == x' IN TRUE\nB == F(v')"
  [.unit 2, .body] [.unit 1, .body, .letDecl 0, .body, .operand 0] (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nIgnore(x) == TRUE\nA == Ignore((v')')"
  [.unit 2, .body, .argument 0, .operand 0] [.unit 2, .body, .argument 0, .operand 0]
  (.atMost (.fixed .action) .state)
#guard reject "Apply(F(_), x) == F(x)" [.unit 0, .parameter 0] (.unsupported .operatorParameter)

#guard failsAt "VARIABLE v\nP == [](v')" [.unit 1, .body, .operand 0] [.unit 1, .body, .operand 0]
  (.nonAction (.fixed .action))
#guard failsAt "VARIABLE v\nB == [v' = v]_v\nP == []B"
  [.unit 2, .body, .operand 0] [.unit 2, .body, .operand 0] (.nonAction (.fixed .action))
#guard failsAt "VARIABLE v\nP == [](LET A == v' IN A)"
  [.unit 1, .body, .operand 0] [.unit 1, .body, .operand 0] (.nonAction (.fixed .action))
#guard failsAt "VARIABLE v\nP == (v' /\\ []v)" [.unit 1, .body] [.unit 1, .body]
  (.noMixedActionTemporal [.fixed .action, .fixed .temporal])
#guard failsAt "VARIABLE v\nMix(p,q) == p /\\ q\nBad == Mix(v', []v)" [.unit 2, .body] [.unit 1, .body]
  (.noMixedActionTemporal [.fixed .action, .fixed .temporal])
#guard failsAt "VARIABLE v\nP == \\E q \\in {v'}: []TRUE"
  [.unit 1, .body, .bound 0, .domain] [.unit 1, .body, .bound 0, .domain]
  (.temporalQuantifierBound (.fixed .temporal) (.fixed .action))
#guard failsAt "VARIABLE v\nP == [v']_(v')" [.unit 1, .body, .operand 1] [.unit 1, .body, .operand 1]
  (.atMost (.fixed .action) .state)
#guard failsAt "VARIABLE v\nP == {[]v}" [.unit 1, .body, .operand 0] [.unit 1, .body, .operand 0]
  (.atMost (.fixed .temporal) .action)

#guard match checkText
    "VARIABLE v\nA == ENABLED (v' = v)\nB == UNCHANGED v\nC == <><<v' = v>>_v\n\
     D == \\E q \\in {v}: []TRUE" with
  | some (.ok result) =>
    bodyHas result 1 .state && bodyHas result 2 .action &&
    bodyHas result 3 .temporal && bodyHas result 4 .temporal
  | _ => false

private def imports (body : String) : Option CheckedRegistry := do
  let root ← parse "Root" s!"EXTENDS Library\n{body}"
  let lib ← parse "Library" "EXTENDS Std\nLOCAL Primed(x) == x'\nPass(p) == Primed(p)"
  (resolveWith .levelSyntax
    [("root", .parsed root [("Library", "lib")]), ("lib", .parsed lib [("Std", "std")]),
     ("std", .signature "Std" [] [.operator (.ident "External") [.expression]])] "root").toOption

private def externalId : BindingId := .declared ⟨"std", [.member 0]⟩
private def externalSignature : ExternalSignature := ⟨.state, [⟨.state, false⟩]⟩

#guard match imports "VARIABLE v\nA == Pass(External(v))\nB == External(v)" with
  | some registry => match check registry [(externalId, externalSignature)] with
    | .ok checked => bodyHas checked 1 .action && bodyHas checked 2 .state
    | .error _ => false
  | none => false

#guard match imports "VARIABLE v\nA == Pass(v')" with
  | some registry => match check registry [(externalId, externalSignature)] with
    | .error error => error =
      ⟨site [.unit 1, .body], .failedRequirement
        ⟨⟨"lib", [.unit 0, .body, .operand 0]⟩, .atMost (.fixed .action) .state⟩⟩
    | .ok _ => false
  | none => false

#guard match imports "VARIABLE v\nA == External(v')" with
  | some registry => match check registry [(externalId, externalSignature)] with
    | .error error => error =
      ⟨site [.unit 1, .body], .failedRequirement
        ⟨⟨"std", [.member 0, .parameter 0]⟩, .atMost (.fixed .action) .state⟩⟩
    | .ok _ => false
  | none => false

private def externalError (table : ExternalLevels) (expected : DiagnosticKind) : Bool :=
  match imports "A == TRUE" with
  | some registry => match check registry table with
    | .error error => error.kind = expected
    | .ok _ => false
  | none => false

#guard externalError [] (.missingExternalSignature externalId)
#guard externalError [(externalId, ⟨.constant, []⟩)] (.signatureArity externalId 1 0)
#guard externalError [(externalId, externalSignature), (externalId, externalSignature)]
  (.duplicateExternalSignature externalId)
#guard externalError [(.builtin (.ident "TRUE"), ⟨.state, []⟩)]
  (.unexpectedExternalSignature (.builtin (.ident "TRUE")))

private def hourClockSource : String :=
  "EXTENDS Naturals\nVARIABLE hr\nHCini == hr \\in (1 .. 12)\n\
   HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1\nHC == HCini /\\ [][HCnxt]_hr\n\
   THEOREM HC => []HCini"

private def hourClock : Bool := Id.run do
  let some source := parse "HourClock" hourClockSource | return false
  let binary := [.expression, .expression]
  let input : Registry :=
    [("root", .parsed source [("Naturals", "naturals")]),
     ("naturals", .signature "Naturals" []
       [.operator (.symbol .infix "..") binary, .operator (.symbol .infix "+") binary])]
  let .ok resolved := resolveWith .levelSyntax input "root" | return false
  let levels : ExternalSignature := ⟨.constant, [⟨.action, true⟩, ⟨.action, true⟩]⟩
  let .ok result := check resolved
    [(.declared ⟨"naturals", [.member 0]⟩, levels), (.declared ⟨"naturals", [.member 1]⟩, levels)]
    | return false
  return bodyHas result 1 .state && bodyHas result 2 .action &&
    bodyHas result 3 .temporal && bodyHas result 4 .temporal &&
    (result.operatorAt (declared [.unit 4])).isNone

#guard hourClock
#guard (resolveText "THEOREM FALSE OBVIOUS").isNone
#guard (resolveText "THEOREM T == TRUE").isNone
#guard (resolveText "I == INSTANCE Library").isNone

end Silmaril.Logic.Temporal.TLA.Resolution.Levels.Examples
