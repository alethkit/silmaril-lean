module

import Silmaril.Logic.Temporal.TLA.Resolution.Defs
meta import Silmaril.Logic.Temporal.TLA.Resolution.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Parser-to-resolver regressions and direct Surface examples. -/

namespace Silmaril.Logic.Temporal.TLA.Resolution.Examples

open Surface

private def parsed (name body : String) : Option Surface.Module :=
  (Parser.parseModule s!"---- MODULE {name} ----\n{body}\n====\n").toOption

private def resolveText (body : String) : Option (Except Diagnostic CheckedRegistry) :=
  (parsed "Sample" body).map (fun source => resolve [("sample", .parsed source [])] "sample")

private def rejects (body : String) (path : Path) (kind : DiagnosticKind) : Bool :=
  match resolveText body with
  | some (.error error) => error = ⟨⟨"sample", path⟩, kind⟩
  | _ => false

private def declared (id : ModuleId) (path : Path) : BindingId :=
  .declared ⟨id, path⟩

private def useIs (checked : CheckedModule) (path : Path) (id : BindingId)
    (role : ReferenceRole := .application) : Bool :=
  checked.referenceAt path = some ⟨id, role⟩

private def closedReferences (checked : CheckedRegistry) : Bool :=
  checked.modules.all fun (_, mod) =>
    mod.references.all (fun (_, use) => (checked.findBinding use.target).isSome) &&
    decide ((mod.references.map Prod.fst).Nodup) &&
    decide ((mod.bindings.map Binding.id).Nodup)

private def checkLet : Bool := Id.run do
  let some (.ok checked) := resolveText
    "CONSTANT Seed\nVARIABLE v\nLOCAL Echo(x) == x\nApply(F(_), y) == F(y)\n\
    Out == LET Check(arg) == Apply(Echo, arg)\n\
               Next == Check(Seed)\n\
           IN <<Next, Apply(LAMBDA z: Echo(z), Seed), v'>>"
    | return false
  let some mod := checked.moduleAt checked.root | return false
  let own := declared "sample"
  let out := [.unit 4, .body]
  let lambda := out ++ [.body, .operand 1, .argument 0]
  return closedReferences checked &&
    useIs mod [.unit 3, .body] (own [.unit 3, .parameter 0]) &&
    useIs mod [.unit 3, .body, .argument 0] (own [.unit 3, .parameter 1]) &&
    useIs mod (out ++ [.letDecl 0, .body, .argument 0]) (own [.unit 2]) .operatorArgument &&
    useIs mod (out ++ [.body, .operand 0]) (own (out ++ [.letDecl 1])) &&
    useIs mod (lambda ++ [.body, .argument 0]) (own (lambda ++ [.parameter 0])) &&
    useIs mod (out ++ [.body, .operand 2]) (.builtin (.symbol .postfix "'")) &&
    useIs mod (out ++ [.body, .operand 2, .operand 0]) (own [.unit 1, .member 0]) &&
    (mod.bindingAt (.ident "Echo")).isSome && (mod.bindingAt (.ident "Next")).isNone &&
    decide (mod.exports.map Binding.name = [.ident "Seed", .ident "v", .ident "Apply", .ident "Out"])

#guard checkLet

#guard match resolveText "A == LET B == TRUE IN B\nB == FALSE\nC == B" with
  | some (.ok checked) => (checked.moduleAt "sample").any fun mod =>
    useIs mod [.unit 2, .body] (declared "sample" [.unit 1])
  | _ => false

#guard match resolveText "VARIABLE v\nA == v'\nB == A'" with
  | some (.ok checked) => (checked.moduleAt "sample").any fun mod =>
    useIs mod [.unit 2, .body] (.builtin (.symbol .postfix "'")) &&
    useIs mod [.unit 2, .body, .operand 0] (declared "sample" [.unit 1])
  | _ => false

private def checkBoundAndSymbolic : Bool := Id.run do
  let some (.ok checked) := resolveText
    "CONSTANT S\na \\oplus b == a\nUse(F(_, _)) == F(TRUE, FALSE)\n\
    Collection == {x ⊕ y : <<x, y>> \\in S}\n\
    FromSymbol == Use(⊕)\n\
    Lookup == [i \\in S |-> [answer |-> i]][TRUE].answer"
    | return false
  let some mod := checked.moduleAt checked.root | return false
  let own := declared "sample"
  return closedReferences checked &&
    useIs mod [.unit 3, .body, .bound 0, .domain] (own [.unit 0, .member 0]) &&
    useIs mod [.unit 3, .body, .body] (own [.unit 1]) &&
    useIs mod [.unit 3, .body, .body, .operand 1]
      (own [.unit 3, .body, .bound 0, .binder 1]) &&
    useIs mod [.unit 4, .body, .argument 0] (own [.unit 1]) .operatorArgument &&
    useIs mod [.unit 5, .body, .operand 0, .operand 0, .body, .field 0]
      (own [.unit 5, .body, .operand 0, .operand 0, .bound 0, .binder 0]) &&
    ((mod.bindingAt (.symbol .infix "⊕")).map Binding.id = some (own [.unit 1]))

#guard checkBoundAndSymbolic

private def diamond (body : String) : Option (Except Diagnostic CheckedRegistry) := do
  let base ← parsed "Base" "EXTENDS Naturals\nLOCAL Hidden == 1 + 2\nPublic == Hidden\nCONSTANT C"
  let right ← parsed "Right" "EXTENDS Base"
  let root ← parsed "Root" s!"EXTENDS Left, Right, Base, Right\n{body}"
  return resolve
    [("std/naturals", .signature "Naturals" []
      [.operator (.symbol .infix "+") [.expression, .expression]]),
     ("lib/base", .parsed base [("Naturals", "std/naturals")]),
     ("lib/left", .signature "Left" [("Base", "lib/base")] []),
     ("lib/right", .parsed right [("Base", "lib/base")]),
     ("root", .parsed root [("Left", "lib/left"), ("Right", "lib/right"), ("Base", "lib/base")])]
    "root"

private def checkDiamond : Bool := Id.run do
  let some (.ok checked) :=
    diamond "Hidden == FALSE\nRead == <<Public, C, 1 + 2, Hidden>>" | return false
  let some root := checked.moduleAt "root" | return false
  let some base := checked.moduleAt "lib/base" | return false
  let hidden := declared "lib/base" [.unit 0]
  let exported := declared "lib/base" [.unit 1]
  return closedReferences checked &&
    decide (checked.modules.length = 5) &&
    decide (root.imports = ["lib/left", "lib/right", "lib/base", "lib/right"]) &&
    decide (root.exports.map Binding.id =
      [declared "std/naturals" [.member 0], exported, declared "lib/base" [.unit 2, .member 0],
       declared "root" [.unit 0], declared "root" [.unit 1]]) &&
    useIs base [.unit 1, .body] hidden &&
    useIs root [.unit 1, .body, .operand 0] exported &&
    useIs root [.unit 1, .body, .operand 3] (declared "root" [.unit 0]) &&
    (checked.findBinding hidden).isSome && base.source.isSome &&
    ((checked.moduleAt "std/naturals").any fun mod => mod.source.isNone)

#guard checkDiamond

#guard match diamond "Read == Hidden" with
  | some (.error error) => error = ⟨⟨"root", [.unit 0, .body]⟩, .unknownName (.ident "Hidden")⟩
  | _ => false

private def fails (registry : Registry) (path : Path) (kind : DiagnosticKind) : Bool :=
  match resolve registry "root" with
  | .error error => error = ⟨⟨"root", path⟩, kind⟩
  | .ok _ => false

private def rootImports (names : List Ident) (links : ImportMap) : ModuleId × ModuleInput :=
  ("root", .parsed ⟨"Root", names, []⟩ links)

#guard fails
  [rootImports ["Left", "Right"] [("Left", "left"), ("Right", "right")],
   ("left", .signature "Left" [] [.constant (.ident "C" 0)]),
   ("right", .signature "Right" [] [.constant (.ident "C" 0)])]
  [.import_ 1] (.conflictingImport (.ident "C") (declared "left" [.member 0])
    (declared "right" [.member 0]))
#guard fails [rootImports ["Naturals"] [], ("naturals", .signature "Naturals" [] [])]
  [.import_ 0] (.unresolvedImport "Naturals")
#guard fails [rootImports ["Other"] [("Other", "absent")]]
  [.import_ 0] (.unknownModule "absent")
#guard fails [rootImports ["Other"] [("Other", "root")]]
  [.import_ 0] (.importNameMismatch "Other" "Root" "root")
#guard fails [rootImports ["Root"] [("Root", "root")]]
  [.import_ 0] (.importCycle ["root", "root"])
#guard fails [rootImports ["Root"] [("Root", "root"), ("Root", "other")]]
  [.import_ 0] (.duplicateImportMapping "Root")
#guard fails [rootImports [] [], rootImports [] []] [] (.duplicateModuleId "root")
#guard fails [("root", .signature "Root" [] [.operator (.ident "F") [.operator 0]])]
  [.member 0] (.malformed "zero-arity operator slot")
#guard match resolve [
    rootImports ["Other"] [("Other", "other")],
    ("other", .signature "Other" [("Root", "root")] [])] "root" with
  | .error error => error = ⟨⟨"other", [.import_ 0]⟩, .importCycle ["root", "other", "root"]⟩
  | .ok _ => false

#guard rejects "A == B\nB == TRUE" [.unit 0, .body] (.unknownName (.ident "B"))
#guard rejects "A == A" [.unit 0, .body] (.unknownName (.ident "A"))
#guard rejects "A == LET B == C C == TRUE IN B" [.unit 0, .body, .letDecl 0, .body]
  (.unknownName (.ident "C"))
#guard rejects "A == LET B == TRUE IN B\nC == B" [.unit 1, .body] (.unknownName (.ident "B"))
#guard rejects "A == LET B == Missing IN TRUE" [.unit 0, .body, .letDecl 0, .body]
  (.unknownName (.ident "Missing"))
#guard rejects "G == TRUE\nA == LET G == FALSE IN G" [.unit 1, .body, .letDecl 0]
  (.conflictingName (.ident "G") (declared "sample" [.unit 0]))
#guard rejects "CONSTANT c\nG(c) == c" [.unit 1, .parameter 0]
  (.conflictingName (.ident "c") (declared "sample" [.unit 0, .member 0]))
#guard rejects "G(G) == G" [.unit 0, .parameter 0]
  (.conflictingName (.ident "G") (declared "sample" [.unit 0]))
#guard rejects "CONSTANT TRUE" [.unit 0, .member 0]
  (.conflictingName (.ident "TRUE") (.builtin (.ident "TRUE")))
#guard rejects "P == \\A a \\in {1}, b \\in {a}: a = b" [.unit 0, .body, .bound 1, .domain, .operand 0]
  (.unknownName (.ident "a"))
#guard rejects "CONSTANT S\nP == \\A <<x, x>> \\in S: TRUE" [.unit 1, .body, .bound 0, .binder 1]
  (.conflictingName (.ident "x") (declared "sample" [.unit 1, .body, .bound 0, .binder 0]))

#guard rejects "Id(x) == x\nA == Id(TRUE, FALSE)" [.unit 1, .body] (.arityMismatch (.ident "Id") 1 2)
#guard rejects "Id(x) == x\nA == Id" [.unit 1, .body] (.arityMismatch (.ident "Id") 1 0)
#guard rejects "Id(x) == x\nA == Id(LAMBDA z: z)" [.unit 1, .body, .argument 0] .expectedExpression
#guard rejects "H(F(_)) == F(TRUE)\nA == H(<<TRUE>>)" [.unit 1, .body, .argument 0]
  (.expectedOperatorArgument 1)
#guard rejects "H(F(_)) == F(TRUE)\nG(a, b) == a\nA == H(G)" [.unit 2, .body, .argument 0]
  (.operatorArgumentMismatch 1 [.expression, .expression])
#guard rejects "H(F(_)) == F(TRUE)\nG(K(_)) == K(TRUE)\nA == H(G)" [.unit 2, .body, .argument 0]
  (.operatorArgumentMismatch 1 [.operator 1])
#guard rejects "a \\oplus b == a\nc ⊕ d == d" [.unit 1]
  (.conflictingName (.symbol .infix "⊕") (declared "sample" [.unit 0]))
#guard rejects "A == 1 + 2" [.unit 0, .body] (.unknownName (.symbol .infix "+"))

#guard rejects "THEOREM FALSE OBVIOUS" [.unit 0] (.unsupported .theoremDecl)
#guard rejects "ASSUME TRUE" [.unit 0] (.unsupported .assumption)
#guard rejects "I == INSTANCE Lib WITH C <- TRUE" [.unit 0] (.unsupported .instantiation)
#guard rejects "A == I!P" [.unit 0, .body] (.unsupported .qualifiedReference)
#guard rejects "A == LET RECURSIVE F(_) F(x) == F(x) IN F(TRUE)" [.unit 0, .body, .letDecl 0]
  (.unsupported .recursive)
#guard rejects "F[x \\in {TRUE}] == x" [.unit 0] (.unsupported .functionDefinition)
#guard rejects "A == [f EXCEPT ![TRUE] = @]" [.unit 0, .body] (.unsupported .except)
#guard rejects "A == []TRUE" [.unit 0, .body] (.unsupported .actionOrTemporal)

#guard match resolve [("root", .parsed ⟨"Root", [], [.variables []]⟩ [])] "root" with
  | .error error => error = ⟨⟨"root", [.unit 0]⟩, .malformed "empty VARIABLE declaration"⟩
  | .ok _ => false

end Silmaril.Logic.Temporal.TLA.Resolution.Examples
