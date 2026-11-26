module

import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
import all Silmaril.Logic.Temporal.TLA.Surface.Examples
meta import all Silmaril.Logic.Temporal.TLA.Surface.Examples
import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs
meta import Silmaril.ProofFormats.TLA.SurfaceSExp.Defs

open Silmaril.Logic.Temporal.TLA.Surface
open Silmaril.Logic.Temporal.TLA.Surface.Parser
open Silmaril.Logic.Temporal.TLA.Surface.Examples (boundedQueue)
open Silmaril.ProofFormats.TLA.SurfaceSExp (encodeExpr encodeModule)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def requireParsed {α : Type} (label : String) (result : Except Diagnostic α) : IO α :=
  match result with
  | .ok parsed => pure parsed
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

private def expr (source : String) : IO Expr := requireParsed source (parseExpr source)

private def definitionBody (parsed : Module) (name : String) : IO Expr := do
  for unit in parsed.units do
    if let .definition (.operator _ (.ident head _) body) := unit then
      if head == name then return body
  throw (IO.userError s!"{parsed.name}: missing definition {name}")

private def checkOperators : IO Unit := do
  match ← expr "-x^2 + y * z" with
  | .infix (.symbol "+") (.prefix .minus (.infix (.symbol "^") _ _)) (.infix (.symbol "*") _ _) => pure ()
  | value => throw (IO.userError s!"unexpected precedence: {reprStr value}")
  match ← expr "a $ b :> c" with
  | .infix (.symbol ":>") (.infix (.symbol "$") _ _) _ => pure ()
  | value => throw (IO.userError s!"unexpected interval precedence: {reprStr value}")
  match ← expr "a /\\ b \\land c" with
  | .infix (.symbol "\\land") (.infix (.symbol "/\\") _ _) _ => pure ()
  | value => throw (IO.userError s!"unexpected alias associativity: {reprStr value}")
  match ← expr "(A \\times B) \\X C × D" with
  | .cartesian [.cartesian [_, _], _, _] => pure ()
  | value => throw (IO.userError s!"unexpected Cartesian factors: {reprStr value}")
  match ← expr "f.a[i,j]'.b[<<i,j>>]" with
  | .index (.field (.postfix .prime (.index (.field _ "a") [_, _])) "b") [.tuple [_, _]] => pure ()
  | value => throw (IO.userError s!"unexpected indexing/selection: {reprStr value}")
  match ← expr "f'[i]''" with
  | .postfix .prime (.postfix .prime (.index (.postfix .prime _) [_])) => pure ()
  | value => throw (IO.userError s!"unexpected postfix chain: {reprStr value}")
  match ← expr "F(1..12, 001 . 0020, \\hA5, (a / b) * c, \"雪\\t\\\"\")" with
  | .ref (.operator (.ident "F"))
      [.expr (.infix (.symbol "..") (.literal (.natural 1)) (.literal (.natural 12))),
       .expr (.literal (.decimal 1 "0020")), .expr (.literal (.natural 165)),
       .expr (.infix (.symbol "*") (.infix (.symbol "/") _ _) _),
       .expr (.literal (.string "雪\t\""))] [] => pure ()
  | value => throw (IO.userError s!"unexpected literals/applications: {reprStr value}")

private def checkJunctions : IO Unit := do
  match ← expr "  /\\ \\/ A\n     \\/ B\n  ∧ C\n    /\\ D" with
  | .junction .conjunction [.junction .disjunction [_, _], .infix (.symbol "/\\") _ _] => pure ()
  | value => throw (IO.userError s!"unexpected nested list/continuation: {reprStr value}")
  match ← expr "  /\\ A\n  \\/ B" with
  | .infix (.symbol "\\/") (.junction .conjunction [_]) _ => pure ()
  | value => throw (IO.userError s!"unexpected same-column kind change: {reprStr value}")
  match ← expr "  /\\ A\n /\\ B\n   /\\ C" with
  | .infix (.symbol "/\\") (.infix (.symbol "/\\") (.junction .conjunction [_]) _) _ => pure ()
  | value => throw (IO.userError s!"unexpected dedent: {reprStr value}")
  match ← expr "\t/\\ IF A THEN B\r\n\t     ELSE C\r\n        /\\ D" with
  | .junction .conjunction [.ifThenElse _ _ _, _] => pure ()
  | value => throw (IO.userError s!"unexpected tab alignment: {reprStr value}")

private def checkConstructs : IO Unit := do
  match ← expr "M(x)!Op(y)!1!<<" with
  | .ref (.operator (.ident "M")) [.expr _]
      [.named (.ident "Op") [.expr _], .structural (.operand 1), .structural .left] => pure ()
  | value => throw (IO.userError s!"unexpected qualified reference: {reprStr value}")
  match ← expr "F(+, LAMBDA x,y: x + y)" with
  | .ref (.operator (.ident "F"))
      [.symbolic (.infix (.symbol "+")), .lambda ["x", "y"] (.infix (.symbol "+") _ _)] [] => pure ()
  | value => throw (IO.userError s!"unexpected operator arguments: {reprStr value}")
  match ← expr "LET RECURSIVE F(_) F(x) == [r EXCEPT !.f[x, 2] = @] IN F(0)" with
  | .letIn [.recursive [.ident "F" 1], .definition (.operator .ordinary (.ident "F" [.ident "x" 0])
      (.except _ [⟨[.field "f", .index [_, .literal (.natural 2)]], .oldValue⟩]))]
      (.ref (.operator (.ident "F")) [.expr (.literal (.natural 0))] []) => pure ()
  | value => throw (IO.userError s!"unexpected LET or EXCEPT: {reprStr value}")
  match ← expr "\\A <<x,y>> \\in S, z,w \\in T: CHOOSE u: u = z" with
  | .rigidQuant .forall (.bounded [⟨.tuple ["x", "y"], _⟩, ⟨.names ["z", "w"], _⟩])
      (.choose (.ident "u") none (.infix (.symbol "=") _ _)) => pure ()
  | value => throw (IO.userError s!"unexpected quantifier/CHOOSE shape: {reprStr value}")
  match ← expr "WF_M!F(i)(A) /\\ SF_<<x,y>>(B)" with
  | .infix (.symbol "/\\") (.fairness .weak (.ref _ [] [.named (.ident "F") [.expr _]]) _)
      (.fairness .strong (.tuple [_, _]) _) => pure ()
  | value => throw (IO.userError s!"unexpected fairness form: {reprStr value}")

private def checkDiagnostics : IO Unit := do
  let cases := [
    ("a ∧\r\n\t)", DiagnosticKind.syntax, ⟨8, 2, 9⟩, ⟨9, 2, 10⟩, "expression"),
    ("a * b / c", .precedence, ⟨6, 1, 7⟩, ⟨7, 1, 8⟩, "precedence conflict"),
    ("[]x'", .precedence, ⟨3, 1, 4⟩, ⟨4, 1, 5⟩, "precedence conflict"),
    ("a (*\n", .lexical, ⟨2, 1, 3⟩, ⟨5, 2, 1⟩, "unterminated block comment"),
    ("\"bad\\q\"", .lexical, ⟨4, 1, 5⟩, ⟨6, 1, 7⟩, "invalid string escape"),
    ("  /\\ (x'\n  )", .syntax, ⟨11, 2, 3⟩, ⟨12, 2, 4⟩, "outside the active junction"),
    ("a b", .syntax, ⟨2, 1, 3⟩, ⟨3, 1, 4⟩, "after complete input"),
    ("x +", .syntax, ⟨3, 1, 4⟩, ⟨3, 1, 4⟩, "expression"),
    ("<1>a", .syntax, ⟨0, 1, 1⟩, ⟨4, 1, 5⟩, "outside a hierarchical proof")]
  for (source, kind, start, stop, message) in cases do
    match parseExpr source with
    | .error actual =>
      check (actual.kind == kind && actual.span == ⟨start, stop⟩ &&
        actual.message.contains message) s!"unexpected diagnostic: {reprStr actual}"
    | .ok actual => throw (IO.userError s!"expected rejection of {source}: {reprStr actual}")

private def checkAssignments (boundedPath bitPath : System.FilePath) : IO Unit := do
  let bounded ← requireParsed "BoundedCounter" (parseModule (← IO.FS.readFile boundedPath))
  check (bounded.name == "BoundedCounter" && bounded.units.length == 5) "BoundedCounter module"
  check (bounded.extendsModules == ["Integers", "Sequences", "FiniteSets", "TLC", "Apalache", "Variants"])
    "BoundedCounter EXTENDS"
  match ← definitionBody bounded "step" with
  | .infix (.symbol "/\\") (.infix (.symbol "<") _ (.literal (.natural 2)))
      (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "n")) [] []))
        (.infix (.symbol "+") _ (.literal (.natural 1)))) => pure ()
  | value => throw (IO.userError s!"BoundedCounter step: {reprStr value}")
  let bits ← requireParsed "BitPair" (parseModule (← IO.FS.readFile bitPath))
  check (bits.name == "BitPair" && bits.units.length == 6) "BitPair module"
  match ← definitionBody bits "step" with
  | .rigidQuant .exists (.bounded [⟨.names ["flip"], .setEnum [_, _]⟩])
      (.infix (.symbol "/\\")
        (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "x")) [] [])) _)
        (.infix (.symbol ":=") (.postfix .prime (.ref (.operator (.ident "y")) [] []))
          (.ifThenElse _ (.infix (.symbol "-") _ _) _))) => pure ()
  | value => throw (IO.userError s!"BitPair step: {reprStr value}")

private def name (id : Ident) (args : List Expr := []) : Expr :=
  .ref (.operator (.ident id)) (args.map .expr) []

private def infixOp (op : String) (left right : Expr) : Expr :=
  .infix (.symbol op) left right

private def checkExpr (label : String) (actual expected : Expr) : IO Unit :=
  check (decide (encodeExpr actual = encodeExpr expected)) s!"{label}: wrong tree\n{reprStr actual}"

private def stepRef (level : StepRefLevel) (id : Ident) : Expr :=
  .ref (.step ⟨level, id⟩) [] []

private def proofStepsModule : Module :=
  let truth := name "TRUE"
  let natural := fun n => Expr.literal (.natural n)
  let prep := stepRef (.explicit 3) "prep"
  let currentPrep := stepRef .current "prep"
  let tupleBound : Bound := ⟨.tuple ["x", "y"], name "S"⟩
  let sufficesProof := Proof.steps [⟨⟨.current, none⟩, .have truth⟩]
    ⟨.explicit 5, none⟩ (some .obvious)
  let caseProof := Proof.steps
    [⟨⟨.next, none⟩, .suffices
      (.assumeProve .plain [.newBoundConstant "k" (name "S")] .plain (name "P" [name "k"]))
      (some sufficesProof)⟩] ⟨.explicit 4, none⟩ none
  let proof := Proof.steps
    [ ⟨⟨.explicit 3, some "prep"⟩, .define
        [ .operator .local (.ident "F" [.ident "x" 0]) (name "x"),
          .function .ordinary "G" [⟨.names ["y"], name "S"⟩] (name "F" [name "y"]) ]⟩,
      ⟨⟨.current, some "plain"⟩, .define
        [ .namedInstance .ordinary "H" [] ⟨"M", [⟨.ident "C", .symbolic (.infix (.symbol "+"))⟩]⟩,
          .operator .ordinary (.ident "J" []) (name "F" [natural 0]) ]⟩,
      ⟨⟨.explicit 3, none⟩, .instantiation ⟨"M", [⟨.ident "C", .expr prep⟩]⟩⟩,
      ⟨⟨.explicit 3, none⟩, .have (.ref (.step ⟨.explicit 3, "prep"⟩) [.expr (natural 1)]
        [.named (.ident "Label") [.expr (natural 2)], .structural (.operand 1)])⟩,
      ⟨⟨.explicit 3, none⟩, .take (.bounded [tupleBound, ⟨.names ["z", "w"], name "V"⟩])⟩,
      ⟨⟨.explicit 3, none⟩, .witness
        [ .infix (.symbol "\\in") (.tuple [name "x", name "y"]) (name "S"),
          .ref (.step ⟨.current, "prep"⟩) [] [.structural .body] ]⟩,
      ⟨⟨.current, none⟩, .pick (.unbounded ["p", "q"]) (name "P" [name "p", name "q"])
        (some (.byFacts true ⟨[.moduleName "M", .expr currentPrep], [.expr prep, .moduleName "N"]⟩))⟩,
      ⟨⟨.explicit 3, some "case_label"⟩, .caseOf (name "C") (some caseProof)⟩,
      ⟨⟨.explicit 3, none⟩, .directive (.use true ⟨[.expr prep], [.expr (name "H")]⟩)⟩,
      ⟨⟨.explicit 3, none⟩, .directive (.hide ⟨[], [.expr (name "G")]⟩)⟩,
      ⟨⟨.explicit 3, some "last"⟩, .assert (.assumeProve .plain [.statement (.expr truth)] .plain truth)
        (some (.steps [] ⟨.explicit 9, none⟩ (some .omitted)))⟩ ]
    ⟨.explicit 3, some "end"⟩
    (some (.steps [] ⟨.next, none⟩ (some (.byFacts false ⟨[.expr (stepRef .current "unknown")], []⟩))))
  ⟨"ProofSteps", [],
    [ .theoremDecl ⟨some "T", .expr truth, some proof⟩,
      .theoremDecl ⟨some "U", .expr truth, some (.steps [] ⟨.current, none⟩ none)⟩ ]⟩

private def compatibilityModule : Module :=
  let definition := fun head body => ModuleUnit.definition (.operator .ordinary (.ident head []) body)
  let overlay := infixOp "="
    (.except (name "r") [⟨[.field "v"], infixOp "@@" .oldValue (name "patch")⟩])
    (name "expected")
  let selected := infixOp "="
    (.ref (.operator (.ident "M")) []
      [.named (.symbolic (.infix (.symbol "@@"))) [], .structural (.operand 1), .structural .allBindings])
    (name "wanted")
  let substitution := Expr.letIn
    [.definition (.namedInstance .ordinary "I" []
      ⟨"M", [⟨.ident "F", .expr (.ref (.operator (.symbolic (.infix (.symbol "+")))) [] [])⟩]⟩)]
    (name "I")
  ⟨"Compatibility", [],
    [ .assumption (some "Named") (name "TRUE"),
      definition "Overlay" (.junction .conjunction [overlay, selected]),
      definition "OverlayOrder"
        (infixOp ":=" (infixOp "@@" (infixOp "@@" (name "a") (name "b")) (name "c")) (name "d")),
      definition "UsesOperator" (.ref (.operator (.ident "F")) [.symbolic (.infix (.symbol "×"))] []),
      definition "Tagged" (infixOp "*" (name "a") (.labeled ⟨"Item", ["x"]⟩ (infixOp "+" (name "b") (name "x")))),
      definition "Substitution" substitution,
      .directive (.use false ⟨[], []⟩),
      .submodule ⟨"Child", [], [.variables ["value"]]⟩,
      .theoremDecl ⟨none, .expr (name "TRUE"), some (.steps [] ⟨.explicit 1, none⟩
        (some (.byFacts false ⟨[], []⟩)))⟩,
      .submodule ⟨"Sibling", [], []⟩ ]⟩

private def membershipFormsModule : Module :=
  let definition := fun head body => ModuleUnit.definition (.operator .ordinary (.ident head []) body)
  let nat := fun n => Expr.literal (.natural n)
  let x := name "x"
  let tag := name "tag"
  let tagFunction := fun body => Expr.function [⟨.names ["tag"], name "BOOLEAN"⟩] body
  let member := infixOp "\\in" x (.setEnum [nat 0, nat 1])
  let nestedSet := Expr.setEnum [.index (tagFunction tag) [name "TRUE"]]
  ⟨"MembershipForms", ["Naturals"],
    [ .variables ["x"],
      definition "Property" (.prefix .always (.action .square member x)),
      definition "Flag" (tagFunction (.ifThenElse tag (nat 1) (nat 0))),
      definition "Applied" (.index (name "Flag") [member]),
      definition "Nested" (.action .square (infixOp "\\in" x nestedSet) x) ]⟩

private def referenceFormsModule : Module :=
  let definition := fun head body => ModuleUnit.definition (.operator .ordinary (.ident head []) body)
  let nat := fun n => Expr.literal (.natural n)
  let x := name "x"
  let truth := Statement.expr (name "TRUE")
  let cite := fun level id => some (Proof.byFacts false ⟨[.expr (stepRef (.explicit level) id)], []⟩)
  let inner := Proof.steps [⟨⟨.explicit 3, some "inner"⟩, .assert truth (some .obvious)⟩]
    ⟨.explicit 3, none⟩ (cite 3 "inner")
  let outer := Proof.steps [⟨⟨.explicit 1, some "outer"⟩, .assert truth (some inner)⟩]
    ⟨.explicit 1, none⟩ (cite 1 "outer")
  ⟨"ReferenceForms", ["Naturals"],
    [ .variables ["x"],
      .submodule ⟨"Child", [], [.theoremDecl ⟨some "Claim", truth, some outer⟩]⟩,
      .definition (.namedInstance .ordinary "ChildInstance" [] ⟨"Child", []⟩),
      definition "Step" (infixOp "=" (.postfix .prime x) (infixOp "+" x (nat 1))),
      definition "Spec" (.junction .conjunction
        [.prefix .always (.action .square (name "Step") x),
         .junction .disjunction [.fairness .weak x (name "Step"),
           .fairness .strong (.tuple [x, x]) (name "Step")]]),
      definition "Arithmetic" (infixOp "+" (nat 1) (.labeled ⟨"Term", []⟩
        (infixOp "*" (nat 2) (nat 3)))) ]⟩

private def innerModuleTest : Module :=
  let innerOp := Expr.ref (.operator (.ident "inner")) [] [.named (.ident "op") []]
  ⟨"InnerModuleTest", ["Semantics"],
    [ .submodule ⟨"Inner", [], [.definition (.operator .ordinary (.ident "op" []) (name "TRUE"))]⟩,
      .definition (.namedInstance .ordinary "inner" [] ⟨"Inner", []⟩),
      .theoremDecl ⟨none, .expr (name "RefersTo" [innerOp, .literal (.string "1")]), none⟩,
      .theoremDecl ⟨none, .expr (name "IsLevel" [innerOp, name "ConstantLevel"]), none⟩ ]⟩

private def fairnessTest : Module :=
  let vars := ["x", "y", "z"]
  let refersTo := fun id => name "RefersTo" [name id, .literal (.string id)]
  let theoremOf := fun kind subscript action => ModuleUnit.theoremDecl
    ⟨none, .expr (name "IsLevel" [.fairness kind subscript action, name "TemporalLevel"]), none⟩
  let observation := refersTo "vars"
  let tuple := Expr.tuple (vars.map refersTo)
  let one := Expr.literal (.natural 1)
  ⟨"FairnessTest", ["Semantics"],
    [ .variables vars,
      .definition (.operator .ordinary (.ident "vars" []) (.tuple (vars.map fun id => name id))),
      theoremOf .weak observation one, theoremOf .weak tuple one,
      theoremOf .strong observation one, theoremOf .strong tuple one,
      theoremOf .weak observation (refersTo "x"), theoremOf .strong observation (refersTo "y"),
      theoremOf .weak observation (.postfix .prime (refersTo "z")),
      theoremOf .strong observation (.postfix .prime (refersTo "x")) ]⟩

private def checkReferenceExpressions : IO Unit := do
  let nat := fun n => Expr.literal (.natural n)
  let condition := infixOp "=" (nat 1) (nat 1)
  checkExpr "prefix minus on a multiplication operand" (← expr "2 * -3^2")
    (infixOp "*" (nat 2) (.prefix .minus (infixOp "^" (nat 3) (nat 2))))
  checkExpr "label precedence ignores operators inside delimited subexpressions"
    (← expr "1 + Term:: 2 * (IF 1 = 1 THEN 3 ELSE 4)")
    (infixOp "+" (nat 1) (.labeled ⟨"Term", []⟩
      (infixOp "*" (nat 2) (.ifThenElse condition (nat 3) (nat 4)))))
  let action := Expr.action .square (name "A") (name "f")
  checkExpr "index outside reduced action subscript" (← expr "[A]_f[i]")
    (.index action [name "i"])
  checkExpr "index inside grouped action subscript" (← expr "[A]_(f[i])")
    (.action .square (name "A") (.index (name "f") [name "i"]))
  checkExpr "explicit action in fairness with a nested reduced subscript" (← expr "WF_[A]_f(i)(B)")
    (.fairness .weak (.action .square (name "A") (name "f" [name "i"])) (name "B"))

private def checkSetExpressions : IO Unit := do
  let x := name "x"
  let y := name "y"
  let s := name "S"
  let t := name "T"
  let p := name "p"
  let one := Expr.literal (.natural 1)
  let member := infixOp "\\in"
  let conjunct := infixOp "/\\"
  let checkForms := fun (forms : List String) (tree : Expr) =>
    forms.forM fun source => do checkExpr source (← expr source) tree
  checkForms ["{<<1, 2>> \\in S}", "{(<<1, 2>> \\in S)}"]
    (.setEnum [member (.tuple [one, .literal (.natural 2)]) s])
  checkForms ["{<<x, y>> \\in S}", "{(<<x, y>> \\in S)}"]
    (.setEnum [member (.tuple [x, y]) s])
  checkForms ["{x \\in S /\\ p}", "{(x \\in S) /\\ p}"]
    (.setEnum [conjunct (member x s) p])
  checkForms ["{x \\in (S /\\ p)}"] (.setEnum [member x (conjunct s p)])
  checkForms ["{1 \\in S : x \\in T}", "{(1 \\in S) : x \\in T}"]
    (.setMap (member one s) [⟨.names ["x"], t⟩])
  checkForms ["{1 ∈ S : x \\in T}"] (.setMap (infixOp "∈" one s) [⟨.names ["x"], t⟩])
  checkForms ["{x \\in S /\\ p : q}"] (.setFilter (.ident "x") (conjunct s p) (name "q"))
  checkForms ["{x \\in S : x \\in T}"] (.setFilter (.ident "x") s (member x t))
  checkForms ["{x \\in S \\in T : p}"] (.setFilter (.ident "x") (member s t) p)
  checkForms ["{<<x, y>> ∈ S : p}"] (.setFilter (.tuple ["x", "y"]) s p)
  checkForms ["{x, y \\in S}"] (.setEnum [x, member y s])
  checkForms ["{F(x,y) : x,y \\in S, <<a,b>> \\in T}"]
    (.setMap (name "F" [x, y]) [⟨.names ["x", "y"], s⟩, ⟨.tuple ["a", "b"], t⟩])
  checkForms ["{<<x, 1>> \\in S : y \\in T}", "{(<<x, 1>> \\in S) : y \\in T}"]
    (.setMap (member (.tuple [x, one]) s) [⟨.names ["y"], t⟩])
  let inLet := Expr.letIn
    [.definition (.operator .ordinary (.ident "A" []) (.choose (.ident "y") none y))]
  checkForms ["{x \\in LET A == CHOOSE y : y IN A}"] (.setEnum [member x (inLet (name "A"))])
  checkForms ["{x \\in LET A == CHOOSE y : y IN A : p}"]
    (.setFilter (.ident "x") (inLet (name "A")) p)
  let selectorDomain := Expr.ref (.operator (.ident "A")) [] [.structural .body]
  checkForms ["{x \\in A!:}"] (.setEnum [member x selectorDomain])
  checkForms ["{x \\in A!: : p}"] (.setFilter (.ident "x") selectorDomain p)
  let recordDomain := Expr.recordSet [⟨"field", s⟩]
  checkForms ["{x \\in [field : S]}"] (.setEnum [member x recordDomain])
  checkForms ["{x \\in [field : S] : p}"] (.setFilter (.ident "x") recordDomain p)
  checkForms ["{x \\in r.CHOOSE : p}"] (.setFilter (.ident "x") (.field (name "r") "CHOOSE") p)
  checkForms ["/\\ {x \\in {y \\in T : p} :\n      /\\ p\n      /\\ q}\n/\\ r"]
    (.junction .conjunction [.setFilter (.ident "x") (.setFilter (.ident "y") t p)
      (.junction .conjunction [p, name "q"]), name "r"])
  let nested := List.range 24 |>.foldl (fun source _ => "{x \\in LET A == CHOOSE y : y IN " ++ source ++ "}") "S"
  let nestedTree := List.range 24 |>.foldl (fun tree _ => .setEnum [member x (inLet tree)]) s
  checkForms [nested] nestedTree

private def checkUpstreamShape (parsed : Module) : IO Unit := do
  if parsed.name == "HourClock" then
    match parsed.units with
    | [.variables ["hr"], .definition _, .definition _, .definition _,
        .theoremDecl ⟨none, .expr (.infix (.symbol "=>") _ (.prefix .always _)), none⟩] =>
      match ← definitionBody parsed "HC" with
      | .infix (.symbol "/\\") _ (.prefix .always (.action .square _ _)) => pure ()
      | value => throw (IO.userError s!"HourClock HC: {reprStr value}")
    | units => throw (IO.userError s!"HourClock units: {reprStr units}")
  else if parsed.name == "LiveHourClock" then
    check (parsed.units.length == 7) "LiveHourClock unit count"
    match ← definitionBody parsed "LSpec", ← definitionBody parsed "AlwaysTick",
        ← definitionBody parsed "PostCondition" with
    | .infix (.symbol "/\\") _ (.fairness .weak _ _),
      .prefix .always (.prefix .eventually (.action .angle _ _)),
      .infix (.symbol "=") _ (.record [⟨"action", .setEnum events⟩, ⟨"state", .setEnum states⟩]) =>
      check (events.length == 12 && states.length == 12) "LiveHourClock trace fixture"
    | _, _, _ => throw (IO.userError "LiveHourClock expression shapes")
  else if parsed.name == "DieHard" then
    check (parsed.units.length == 16) "DieHard unit count"
    match ← definitionBody parsed "Init", ← definitionBody parsed "FixWater" with
    | .junction .conjunction [_, _, _, _], .junction .disjunction items =>
      check (items.length == 6 && items.all (fun
        | .junction .conjunction [_, _, _] | .junction .conjunction [_, _, _, _] => true
        | _ => false)) "DieHard nested junction lists"
    | _, _ => throw (IO.userError "DieHard expression shapes")
  else if parsed.name == "ACP_SB" then
    let vars := Expr.tuple [name "coordinator", name "participant"]
    checkExpr "ACP_SB fairness" (← definitionBody parsed "fairness")
      (.junction .conjunction [
        .rigidQuant .forall (.bounded [⟨.names ["i"], name "participants"⟩])
          (.fairness .weak vars (name "parProg" [name "i"])),
        .fairness .weak vars (name "coordProgB")])
  else if parsed.name == "EWD840" then
    let str := fun s => Expr.literal (.string s)
    checkExpr "EWD840 Inv" (← definitionBody parsed "Inv")
      (.junction .disjunction [
        .labeled ⟨"P0", []⟩ (.rigidQuant .forall (.bounded [⟨.names ["i"], name "Node"⟩])
          (infixOp "=>" (infixOp "<" (name "tpos") (name "i"))
            (.prefix .negation (.index (name "active") [name "i"])))),
        .labeled ⟨"P1", []⟩ (.rigidQuant .exists
          (.bounded [⟨.names ["j"], infixOp ".." (.literal (.natural 0)) (name "tpos")⟩])
          (infixOp "=" (.index (name "color") [name "j"]) (str "black"))),
        .labeled ⟨"P2", []⟩ (infixOp "=" (name "tcolor") (str "black"))])

private def checkCorpus : List String → IO Unit
  | [] => pure ()
  | file :: expected :: rest => do
    let source ← IO.FS.readFile file
    match parseModule source with
    | .ok parsed =>
      check (expected == "accept") s!"{file}: unexpectedly accepted"
      let expectedTree := match (System.FilePath.mk file).fileName with
        | some "BoundedQueue.tla" => some boundedQueue
        | some "ProofSteps.tla" => some proofStepsModule
        | some "Compatibility.tla" => some compatibilityModule
        | some "MembershipForms.tla" => some membershipFormsModule
        | some "ReferenceForms.tla" => some referenceFormsModule
        | some "InnerModuleTest.tla" => some innerModuleTest
        | some "FairnessTest.tla" => some fairnessTest
        | _ => none
      match expectedTree with
      | some tree =>
        check (decide (encodeModule parsed = encodeModule tree)) s!"{file}: wrong tree\n{reprStr parsed}"
      | none => checkUpstreamShape parsed
    | .error error =>
      let actual := if error.kind == .unsupported then "unsupported" else "reject"
      check (actual == expected) s!"{file}: {reprStr error}"
    checkCorpus rest
  | _ => throw (IO.userError "supply path/verdict pairs")

private def checkModuleShape : IO Unit := do
  let source := "(* lead (* nested *) *)\n---- MODULE Parent ----\n\
    EXTENDS Base\nCONSTANT C, F(_)\n---- MODULE Child ----\n\
    VARIABLE v\n====\nLOCAL I(x) == INSTANCE Child WITH v <- x\n\
    LEMMA T == ASSUME NEW x \\in C, NEW VARIABLE w PROVE F(x) BY ONLY F(x) DEF F\n\
    ==== \\* trailing comment"
  let parsed ← requireParsed "module with nested unit and proof" (parseModule source)
  match parsed with
  | ⟨"Parent", ["Base"], [.constants [.ident "C" 0, .ident "F" 1],
      .submodule ⟨"Child", [], [.variables ["v"]]⟩,
      .definition (.namedInstance .local "I" [.ident "x" 0] ⟨"Child", [⟨.ident "v", _⟩]⟩),
      .theoremDecl ⟨some "T", .assumeProve .plain [.newBoundConstant "x" _, .newVariable "w"] .plain _,
        some (.byFacts true ⟨[.expr _], [.expr _]⟩)⟩]⟩ => pure ()
  | value => throw (IO.userError s!"unexpected module shape: {reprStr value}")

public def main (args : List String) : IO Unit := do
  checkOperators
  checkJunctions
  checkConstructs
  checkReferenceExpressions
  checkSetExpressions
  checkDiagnostics
  checkModuleShape
  let fixtures := System.FilePath.mk "tests/semantics/tla-quint"
  checkAssignments (fixtures / "BoundedCounter.tla") (fixtures / "BitPair.tla")
  checkCorpus args
  IO.println s!"Native TLA+ parser regressions passed ({args.length / 2} corpus modules)"
