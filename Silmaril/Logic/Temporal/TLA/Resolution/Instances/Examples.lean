module

import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Instances.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Parsed regressions for scoped first-order INSTANCE. -/

namespace Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples

open Surface

private def parsed (id : ModuleId) (header body : String) (edges : ImportMap := []) :
    Option (ModuleId × ModuleInput) :=
  (Parser.parseModule s!"---- MODULE {header} ----\n{body}\n====\n").toOption.map
    fun source => (id, .parsed source edges)

private def run (root lib : String) : Option (Except Diagnostic CheckedInstances) := do
  let libSource ← parsed "library" "Lib" lib
  let rootSource ← parsed "root" "Root" root [("Lib", "library")]
  return check [rootSource, libSource] "root"

private def site (id : ModuleId) (path : Path) : Site := ⟨id, path⟩
private def declared (id : ModuleId) (path : Path) : BindingId := .declared (site id path)

private def bodyLevel (answer : CheckedInstances) (id : ModuleId) (unit : Nat)
    (level : Levels.Level) : Bool :=
  answer.levels.expressionAt (site id [.unit unit, .body]) = some (.fixed level)

private def bindingId (answer : CheckedInstances) (id : ModuleId) (name : Name) : Option BindingId :=
  ((answer.registry.moduleAt id).bind (·.bindingAt name)).map Binding.id

private def named : Bool := Id.run do
  let some (.ok answer) := run
    "CONSTANT Spare\nVARIABLE h\nI(t) == INSTANCE Lib WITH C <- t, x <- ~h\n\
     LOCAL J == INSTANCE Lib WITH C <- FALSE, x <- h\nP == I(TRUE)!Out(TRUE)\nQ == J!Next"
    "CONSTANT C, Spare\nVARIABLE x\nLOCAL Hidden(p) == p /\\ C\n\
     Out(z) == Hidden(z) /\\ x\nNext == x'"
    | return false
  let out := declared "root" [.unit 2, .instanceMember 0]
  let next := declared "root" [.unit 3, .instanceMember 1]
  let some (plan, member) := answer.memberAt out | return false
  let some root := answer.registry.moduleAt "root" | return false
  let some home := answer.registry.moduleAt "library" | return false
  let some summary := answer.levels.operatorAt out | return false
  let .some (.expression replacementSite (.prefix .negation _)) :=
    plan.substitutions.lookup (declared "library" [.unit 1, .member 0])
    | return false
  let .some (.binding spare) := plan.substitutions.lookup (declared "library" [.unit 0, .member 1])
    | return false
  return
    decide (member.home = declared "library" [.unit 3] && member.argumentCounts = [1, 1]) &&
    decide (plan.parameters = [declared "root" [.unit 2, .parameter 0]]) &&
    decide (spare = declared "root" [.unit 0, .member 0]) &&
    decide (replacementSite = site "root" [.unit 2, .substitution 1]) &&
    decide (root.referenceAt [.unit 2, .substitution 1, .operand 0] =
      some ⟨declared "root" [.unit 1, .member 0], .application⟩) &&
    decide (home.referenceAt [.unit 3, .body, .operand 0] =
      some ⟨declared "library" [.unit 2], .application⟩) &&
    decide (root.referenceAt [.unit 4, .body] = some ⟨out, .application⟩) &&
    decide (root.referenceAt [.unit 5, .body] = some ⟨next, .application⟩) &&
    decide (summary.maxArgumentLevels = [.constant, .temporal]) &&
    !(root.exports.any fun binding => binding.id = next) &&
    bodyLevel answer "root" 4 .state && bodyLevel answer "root" 5 .action

#guard named

private def nestedRegistry (result : String) : Option Registry := do
  let leaf ← parsed "leaf" "Leaf" "CONSTANT c\nPub(v) == c /\\ v"
  let middle ← parsed "middle" "Middle"
    "CONSTANT d\nInner(q) == INSTANCE Leaf WITH c <- d /\\ q\nWrapped == Inner(TRUE)!Pub(TRUE)"
    [("Leaf", "leaf")]
  let root ← parsed "root" "Root"
    s!"VARIABLE x\nOuter(p) == INSTANCE Middle WITH d <- p\n\
       Other == INSTANCE Middle WITH d <- TRUE\n{result}"
    [("Middle", "middle")]
  return [root, middle, leaf]

private def nested : Bool := Id.run do
  let some registry := nestedRegistry
    "Seen == Outer(x)!Inner(TRUE)!Pub(TRUE)\nOtherSeen == Other!Inner(TRUE)!Pub(TRUE)\nWrappedSeen == Outer(x)!Wrapped"
    | return false
  let .ok answer := check registry "root" | return false
  let some outer := bindingId answer "root" (.qualified ["Outer", "Inner"] (.ident "Pub"))
    | return false
  let some other := bindingId answer "root" (.qualified ["Other", "Inner"] (.ident "Pub"))
    | return false
  let some (outerPlan, outerMember) := answer.memberAt outer | return false
  let some (_, innerMember) := answer.memberAt outerMember.home | return false
  return decide (outer ≠ other) &&
    decide (outerMember.argumentCounts = [1, 1, 1] && outerPlan.target = "middle") &&
    decide (innerMember.home = declared "leaf" [.unit 1]) &&
    bodyLevel answer "root" 3 .state && bodyLevel answer "root" 4 .constant &&
    bodyLevel answer "root" 5 .state && bodyLevel answer "middle" 2 .constant

#guard nested
#guard match nestedRegistry "Bad == Outer(TRUE)!Inner!Pub(TRUE, TRUE)" with
  | some registry => match check registry "root" with
    | .error (.resolution e) => e.site = site "root" [.unit 3, .body, .selector 0] &&
      e.kind = .arityMismatch (.qualified ["Outer", "Inner"] (.ident "Pub")) 1 0
    | _ => false
  | none => false

private def anonymousRegistry (body : String) : Option Registry := do
  let parent ← parsed "parent" "Parent" "CONSTANT C"
  let library ← parsed "library" "Lib" "EXTENDS Parent\nLOCAL H == C\nOut == H"
    [("Parent", "parent")]
  let host ← parsed "host" "Host" "CONSTANT C\nLOCAL INSTANCE Lib\nPub == Out"
    [("Lib", "library")]
  let root ← parsed "root" "Root" s!"EXTENDS Host\n{body}" [("Host", "host")]
  return [parent, library, host, root]

#guard match anonymousRegistry "Read == Pub" with
  | some registry => match check registry "root" with
    | .ok answer =>
      let out := declared "host" [.unit 1, .instanceMember 0]
      match answer.memberAt out with
      | some (plan, member) =>
        decide (member.home = declared "library" [.unit 1]) &&
        (match plan.substitutions with
          | [(target, .binding host)] =>
            target = declared "parent" [.unit 0, .member 0] &&
            host = declared "host" [.unit 0, .member 0]
          | _ => false) &&
        bodyLevel answer "root" 0 .constant &&
        (bindingId answer "root" (.ident "Out")).isNone
      | none => false
    | _ => false
  | none => false

#guard match run "LOCAL INSTANCE Lib\nINSTANCE Lib\nP == Out" "Out == TRUE" with
  | some (.ok answer) =>
    decide (bindingId answer "root" (.ident "Out") = some (declared "library" [.unit 0])) &&
    ((answer.registry.moduleAt "root").any fun mod => mod.exports.any (·.name = .ident "Out"))
  | _ => false

#guard match run "VARIABLE y\nI == INSTANCE Lib WITH x <- y\nP == I!Out"
    "VARIABLE x\nOut == \\E y: x = y" with
  | some (.ok answer) =>
    let hostY := declared "root" [.unit 0, .member 0]
    let homeY := declared "library" [.unit 1, .body, .binder 0]
    match answer.registry.moduleAt "root", answer.registry.moduleAt "library" with
    | some root, some lib =>
      decide (root.referenceAt [.unit 1, .substitution 0] = some ⟨hostY, .application⟩) &&
      decide (lib.referenceAt [.unit 1, .body, .body, .operand 1] = some ⟨homeY, .application⟩) &&
      bodyLevel answer "root" 2 .state
    | _, _ => false
  | _ => false

#guard match (do
    let lib ← parsed "library" "Lib" "CONSTANT C\nOut(x) == C /\\ x"
    let host ← parsed "host" "Host" "I(t) == INSTANCE Lib WITH C <- t" [("Lib", "library")]
    let root ← parsed "root" "Root" "EXTENDS Host\nP == I(TRUE)!Out(FALSE)" [("Host", "host")]
    return check [root, host, lib] "root") with
  | some (.ok answer) => bodyLevel answer "root" 0 .constant &&
    (answer.memberAt (declared "host" [.unit 0, .instanceMember 0])).isSome
  | _ => false

#guard match (do
    let common ← parsed "common" "Common" "CONSTANT C"
    let lib ← parsed "library" "Lib" "EXTENDS Common\nOut == C" [("Common", "common")]
    let root ← parsed "root" "Root" "EXTENDS Common\nINSTANCE Lib\nP == Out"
      [("Common", "common"), ("Lib", "library")]
    return check [root, lib, common] "root") with
  | some (.ok answer) =>
    match answer.instanceAt (site "root" [.unit 0]) with
    | some ⟨_, _, _, [(target, .binding host)], _⟩ =>
      decide (target = declared "common" [.unit 0, .member 0] && host = target) &&
      bodyLevel answer "root" 1 .constant
    | _ => false
  | _ => false

#guard match (do
    let root ← parsed "root" "Root" "INSTANCE Lib" [("Lib", "library")]
    return check [root, ("library", .signature "Lib" [] [])] "root") with
  | some (.error (.resolution e)) => e = ⟨site "root" [.unit 0], .unsupported .instanceSignature⟩
  | _ => false

private def bindingError (root lib : String) (path : Path) (cause : Resolution.DiagnosticKind) :
    Bool :=
  match run root lib with
  | some (.error (.resolution error)) => error = ⟨site "root" path, cause⟩
  | _ => false

#guard bindingError "INSTANCE Lib" "CONSTANT C\nOut == TRUE" [.unit 0]
  (.missingSubstitution (.ident "C") (declared "library" [.unit 0, .member 0]))
#guard bindingError "INSTANCE Lib WITH C <- TRUE, C <- FALSE" "CONSTANT C\nOut == C"
  [.unit 0, .substitution 1] (.duplicateSubstitution (declared "library" [.unit 0, .member 0]))
#guard bindingError "INSTANCE Lib WITH Out <- TRUE" "Out == TRUE"
  [.unit 0, .substitution 0] (.illegalSubstitutionTarget (.ident "Out"))
#guard bindingError "F(x) == x\nINSTANCE Lib WITH C <- F" "CONSTANT C\nOut == C"
  [.unit 1, .substitution 0] (.arityMismatch (.ident "F") 1 0)
#guard bindingError "F(x) == x\nINSTANCE Lib" "CONSTANT F\nOut == F"
  [.unit 1] (.arityMismatch (.ident "F") 0 1)
#guard bindingError "INSTANCE Lib WITH F <- LAMBDA x: x" "CONSTANT F(_)\nOut == F(TRUE)"
  [.unit 0, .substitution 0] (.unsupported .operatorSubstitution)
#guard bindingError "I(F(_)) == INSTANCE Lib" "Out == TRUE"
  [.unit 0, .parameter 0] (.unsupported .instanceParameter)
#guard bindingError "I == INSTANCE Lib\nP == I" "Out == TRUE" [.unit 1, .body]
  (.incompleteInstanceName (.ident "I"))
#guard bindingError "INSTANCE Lib WITH C <- TRUE\nINSTANCE Lib WITH C <- FALSE"
  "CONSTANT C\nOut == C" [.unit 1, .instanceMember 0]
  (.conflictingName (.ident "Out") (declared "root" [.unit 0, .instanceMember 0]))
#guard bindingError "INSTANCE Lib" "THEOREM TRUE\nOut == TRUE" [.unit 0]
  (.unsupported .instanceTheorem)
#guard bindingError "P == LET I == INSTANCE Lib IN I!Out" "Out == TRUE" [.unit 0, .body, .letDecl 0]
  (.unsupported .letInstance)

#guard match (do
    let lib ← parsed "library" "Lib" "EXTENDS Root" [("Root", "root")]
    let host ← parsed "root" "Root" "INSTANCE Lib" [("Lib", "library")]
    return check [lib, host] "root") with
  | some (.error (.resolution e)) => e.kind = .importCycle ["root", "library", "root"]
  | _ => false

private def levelError (root lib : String) (position : Site) (cause : Levels.DiagnosticKind) : Bool :=
  match run root lib with
  | some (.error (.levels error)) => error = ⟨position, cause⟩
  | _ => false

#guard levelError "VARIABLE v\nI == INSTANCE Lib WITH C <- v, x <- v"
  "CONSTANT C\nVARIABLE x\nOut == C /\\ x"
  (site "root" [.unit 1, .substitution 0])
  (.substitutionLevel (declared "library" [.unit 0, .member 0]) .constant .state)

#guard levelError "VARIABLE v\nI == INSTANCE Lib WITH x <- v'"
  "VARIABLE x\nNext == x'"
  (site "root" [.unit 1, .substitution 0])
  (.substitutionLevel (declared "library" [.unit 0, .member 0]) .state .action)

#guard levelError "VARIABLE v\nI(t) == INSTANCE Lib WITH C <- t, x <- v\nBad == I(v)!Out"
  "CONSTANT C\nVARIABLE x\nOut == x"
  (site "root" [.unit 2, .body])
  (.failedRequirement ⟨site "root" [.unit 1, .substitution 0], .atMost (.fixed .state) .constant⟩)

#guard match run "VARIABLE v\nI == INSTANCE Lib WITH C <- v'\nP == I!Out"
    "CONSTANT C\nOut == C" with
  | some (.ok answer) => bodyLevel answer "root" 2 .action && bodyLevel answer "library" 1 .constant
  | _ => false

#guard levelError "VARIABLE v\nI == INSTANCE Lib WITH C <- v'\nP == (I!Out)'"
  "CONSTANT C\nOut == C"
  (site "root" [.unit 2, .body, .operand 0])
  (.failedRequirement ⟨site "root" [.unit 2, .body, .operand 0], .atMost (.fixed .action) .state⟩)

#guard levelError "VARIABLE v\nI == INSTANCE Lib WITH C <- []v"
  "CONSTANT C\nOut == {C}"
  (site "root" [.unit 1])
  (.instanceReplay (site "library" [.unit 1, .body, .operand 0])
    (.failedRequirement ⟨site "library" [.unit 1, .body, .operand 0],
      .atMost (.fixed .temporal) .action⟩))

#guard levelError "VARIABLE v\nINSTANCE Lib WITH x <- v"
  "VARIABLE x\nCan == ENABLED (x' = x)"
  (site "root" [.unit 1])
  (.instanceReplay (site "library" [.unit 1, .body]) (.unsupported .instanceImplicitBinding))

private def localReplay (root inner : String) (leafBody : String := "Unused == C /\\ x") :
    Option (Except Diagnostic CheckedInstances) := do
  let leaf ← parsed "leaf" "Leaf" s!"CONSTANT C\nVARIABLE x\n{leafBody}"
  let middle ← parsed "middle" "Middle" s!"CONSTANT d, e\n{inner}\nOut == e"
    [("Leaf", "leaf")]
  let host ← parsed "root" "Root" root [("Middle", "middle")]
  return check [host, middle, leaf] "root"

private def localConstant : String := "LOCAL INSTANCE Leaf WITH C <- d, x <- TRUE"

private def rejectsUnrelatedExport (leafBody : String) : Bool :=
  match localReplay "VARIABLE v\nI(t) == INSTANCE Middle WITH d <- t, e <- TRUE\nBad == I(v)!Out"
      localConstant leafBody with
  | some (.error (.levels error)) => error =
      ⟨site "root" [.unit 2, .body], .failedRequirement
        ⟨site "middle" [.unit 1, .substitution 0], .atMost (.fixed .state) .constant⟩⟩
  | _ => false

#guard rejectsUnrelatedExport "Unused == C /\\ x"
#guard rejectsUnrelatedExport "LOCAL Private == x"
#guard rejectsUnrelatedExport ""

#guard match localReplay
    "VARIABLE v\nI(t) == INSTANCE Middle WITH d <- t, e <- TRUE\n\
     J(t) == INSTANCE Middle WITH d <- TRUE, e <- t\nA == I(TRUE)!Out\nB == J(v)!Out"
    localConstant with
  | some (.ok answer) =>
    let i := answer.levels.operatorAt (declared "root" [.unit 1, .instanceMember 0])
    let j := answer.levels.operatorAt (declared "root" [.unit 2, .instanceMember 0])
    decide (i.map Levels.OperatorSummary.maxArgumentLevels = some [.constant]) &&
    decide (j.map Levels.OperatorSummary.maxArgumentLevels = some [.temporal]) &&
    bodyLevel answer "root" 3 .constant && bodyLevel answer "root" 4 .state
  | _ => false

#guard match localReplay
    "VARIABLE v\nI(t) == INSTANCE Middle WITH d <- t, e <- TRUE\n\
     J(t) == INSTANCE Middle WITH d <- TRUE, e <- t\nGood == J(v)!Out\nBad == I(v)!Out"
    localConstant with
  | some (.error (.levels error)) => error =
      ⟨site "root" [.unit 4, .body], .failedRequirement
        ⟨site "middle" [.unit 1, .substitution 0], .atMost (.fixed .state) .constant⟩⟩
  | _ => false

private def localNamed : String := "LOCAL J(q) == INSTANCE Leaf WITH C <- q, x <- d"

#guard match localReplay
    "VARIABLE v\nI(t) == INSTANCE Middle WITH d <- t, e <- TRUE\nGood == I(v)!Out"
    localNamed "" with
  | some (.ok answer) =>
    let i := answer.levels.operatorAt (declared "root" [.unit 1, .instanceMember 0])
    decide (i.map Levels.OperatorSummary.maxArgumentLevels = some [.state]) &&
    decide (i.map Levels.OperatorSummary.requirements = some [
      ⟨site "middle" [.unit 1, .substitution 1],
        .atMost (.parameter (declared "root" [.unit 1, .parameter 0])) .state⟩]) &&
    bodyLevel answer "root" 2 .constant
  | _ => false

#guard match localReplay
    "VARIABLE v\nI(t) == INSTANCE Middle WITH d <- t, e <- TRUE\nBad == I(v')!Out"
    localNamed "" with
  | some (.error (.levels error)) => error =
      ⟨site "root" [.unit 2, .body], .failedRequirement
        ⟨site "middle" [.unit 1, .substitution 1], .atMost (.fixed .action) .state⟩⟩
  | _ => false

end Silmaril.Logic.Temporal.TLA.Resolution.Instances.Examples
