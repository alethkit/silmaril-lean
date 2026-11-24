module

public meta import Lean.Data.Json
public meta import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Model.Thms

public meta section
open Lean
open Silmaril.Logic.Smt (SE)
open Silmaril.ProofFormats
open Silmaril.ProofFormats.DaslSyntax
open Silmaril.ProofFormats.DaslSyntax.Database

namespace NamedLogicExport

open Silmaril.Logic.HOLLight (Tm Model Valid)

mutual
def tree : SE → Json
  | .atom text => .str text
  | .list children => .arr (trees children).toArray

def trees : List SE → List Json
  | [] => []
  | child :: children => tree child :: trees children
end

def block {Item : Type} (grammar : Syntax Item) (item : Item) : Json :=
  tree (grammar.codec.encode item)

def evidencePath := "Silmaril/ProofFormats/DaslSyntax/Database/Examples/Thms.lean"

def step {Checked : Prop} (_checked : Checked) (declaration : Name)
    (id rule judgment : String) (premises : List String := []) : Json :=
  Json.mkObj [("id", toJson id), ("rule", toJson rule), ("judgment", toJson judgment),
    ("premises", toJson premises), ("declaration", toJson declaration.toString)]

def row {Checked : Prop} (_checked : Checked) (declaration : Name)
    (id logic judgment scope : String) (roots : List (String × String))
    (assumptions : List String := []) (steps : List Json := []) : Json :=
  Json.mkObj [("id", toJson id), ("logic", toJson logic), ("judgment", toJson judgment),
    ("scope", toJson scope), ("roots", Json.mkObj (roots.map fun (role, key) => (role, toJson key))),
    ("assumptions", toJson assumptions), ("evidence", Json.mkObj [("declaration", toJson declaration.toString),
      ("path", toJson evidencePath), ("steps", toJson steps)])]

def source (revision : String) : Json :=
  Json.mkObj [("repo", "hiloopai/silmaril-lean"), ("revision", toJson revision)]

def closedKey := "hol.closed"

/-- Both proof arguments are checked against the very term supplied to the grammar encoder. -/
def closedClaims (revision : String) (p : Tm)
    (_derivable : Database.HOL.ClosedProof Silmaril.Logic.HOLLight.initialSignature [] p)
    (_valid : Valid Model.standard.{0} p) : Json × Json :=
  let logic := "hol-light.initial.v1"
  let derivability := "hol-light.kernel.v1"
  let standard := "hol-light.standard.u0.v1"
  let derivesId := "hol.closed.derivability.v1"
  let validId := "hol.closed.standard-validity.v1"
  let named (n : Name) := toJson n.toString
  let empty := Json.arr #[]
  let claim := fun interpretation mode valuation => Json.mkObj [
    ("logic", toJson logic), ("interpretation", toJson interpretation), ("mode", toJson mode),
    ("roots", Json.arr #[Json.mkObj [("role", "conclusion"), ("syntax", toJson closedKey)]]),
    ("context", Json.mkObj [("kind", "empty")]), ("assumptions", empty),
    ("scope", Json.mkObj [("termVariables", "closed"), ("valuation", toJson valuation)])]
  let table := fun title rowId claimId label => Json.mkObj [
    ("logic", toJson logic), ("title", toJson title),
    ("rows", Json.arr #[Json.mkObj [("id", toJson rowId), ("claim", toJson claimId), ("label", toJson label)]])]
  let evidence := fun (decl : Name) (path : String) => Json.arr #[Json.mkObj [
    ("kind", "lean-theorem"), ("source", source revision), ("declaration", named decl), ("path", toJson path)]]
  let index := Json.mkObj [
    ("syntax", Json.mkObj [(closedKey, toJson closedKey)]),
    ("logics", Json.mkObj [(logic, Json.mkObj [
      ("family", "hol"), ("signature", named ``Silmaril.Logic.HOLLight.initialSignature),
      ("theory", Json.mkObj [("kind", "explicit"), ("axioms", empty)])])]),
    ("interpretations", Json.mkObj [
      (derivability, Json.mkObj [("kind", "derivability"), ("logic", toJson logic),
        ("calculus", named ``Silmaril.Logic.HOLLight.Derives),
        ("predicate", named ``Database.HOL.ClosedProof)]),
      (standard, Json.mkObj [("kind", "model"), ("logic", toJson logic),
        ("construction", named ``Model.standard), ("universe", toJson (0 : Nat)),
        ("predicate", named ``Valid), ("source", source revision),
        ("path", "Silmaril/Logic/HOLLight/Consistency.lean"),
        ("leanVersion", toJson Lean.versionString),
        ("imports", toJson (["Silmaril.Logic.HOLLight.Consistency"] : List String))])]),
    ("claims", Json.mkObj [
      (derivesId, claim derivability "derivability" "schematic-types"),
      (validId, claim standard "validity" "all-type-and-free-term-valuations")]),
    ("tables", Json.mkObj [
      ("closed-theorems", table "Closed theorems" closedKey derivesId "∅ ⊢ truth ⇒ truth"),
      ("standard-model-validity", table "Standard model validity" "hol.closed.standard" validId "truth ⇒ truth")]),
    ("evidence", Json.mkObj [
      (derivesId, evidence ``Examples.HOL.closedProof evidencePath),
      (validId, evidence ``Examples.HOL.standardValidity
        "Silmaril/ProofFormats/DaslSyntax/Database/Examples/Model/Thms.lean")])]
  (block DaslSyntax.HOL.tm p, index)

def plan (revision : String) (withInterpretations : Bool := false) : Json :=
  let (closedBlock, claimIndex) :=
    closedClaims revision Examples.HOL.closed Examples.HOL.closedProof Examples.HOL.standardValidity
  let holScope := "HOL Light initialSignature; empty added theory"
  let mlttScope := "Extensional MLTT; empty context; Sigma formation at U₀"
  let sigmaText := "Σ n : ℕ, Id ℕ n n"
  let pairText := "(zero, refl zero)"
  let holAssume := step Examples.HOL.assumed ``Examples.HOL.assumed "assume" "assume" "{p} ⊢ p"
  let sigmaForm := step Examples.MLTT.sigmaFormation ``Examples.MLTT.sigmaFormation
    "sigma" "dependent sum formation" s!"⊢ {sigmaText} : U₀"
  let pairTyping := step Examples.MLTT.pairTyping ``Examples.MLTT.pairTyping
    "pair" "dependent pair" s!"⊢ {pairText} : {sigmaText}" ["sigma"]
  Json.mkObj <| [
    ("format", toJson (if withInterpretations then "silmaril.named-logic.plan.v2" else "silmaril.named-logic.plan.v1")),
    ("source", source revision),
    ("blocks", Json.mkObj [
      (closedKey, closedBlock),
      ("hol.assumptions", block DaslSyntax.HOL.assumptions [Examples.HOL.premise]),
      ("hol.premise", block DaslSyntax.HOL.tm Examples.HOL.premise),
      ("hol.consequence", block DaslSyntax.HOL.tm Examples.HOL.consequence),
      ("mltt.context", block DaslSyntax.MLTT.ctx .nil),
      ("mltt.sigma", block DaslSyntax.MLTT.ty Examples.MLTT.sigma),
      ("mltt.pair", block (DaslSyntax.MLTT.tm 0) Examples.MLTT.pair),
      ("mltt.first", block (DaslSyntax.MLTT.tm 0) (.fst Examples.MLTT.pair)),
      ("mltt.second", block (DaslSyntax.MLTT.tm 0) (.snd Examples.MLTT.pair)),
      ("mltt.nat", block DaslSyntax.MLTT.ty .nats),
      ("mltt.zero-fiber", block DaslSyntax.MLTT.ty (Examples.MLTT.fiber.lst .zero))]),
    ("rows", toJson [
      row Examples.HOL.closedRow ``Examples.HOL.closedRow "hol.closed" "HOL" "∅ ⊢ truth ⇒ truth"
        holScope [("conclusion", "hol.closed")] []
        [step Examples.HOL.closedProof ``Examples.HOL.closedProof "closed" "implication introduction"
          "∅ ⊢ truth ⇒ truth"],
      row Examples.HOL.contextRow ``Examples.HOL.contextRow "hol.named-assumption" "HOL" "{p} ⊢ truth ⇒ p"
        holScope [("context", "hol.assumptions"), ("conclusion", "hol.consequence")] ["hol.premise"]
        [holAssume, step Examples.HOL.consequenceProof ``Examples.HOL.consequenceProof "consequence"
          "weakening and implication introduction" "{p} ⊢ truth ⇒ p" ["assume"]],
      row Examples.MLTT.formationRow ``Examples.MLTT.formationRow "mltt.sigma-form" "MLTT"
        s!"⊢ {sigmaText} : U₀" mlttScope [("context", "mltt.context"), ("type", "mltt.sigma")] [] [sigmaForm],
      row Examples.MLTT.inhabitanceRow ``Examples.MLTT.inhabitanceRow "mltt.sigma-inhabited" "MLTT"
        s!"∃ term, ⊢ term : {sigmaText}" mlttScope
        [("context", "mltt.context"), ("type", "mltt.sigma")] [] [sigmaForm, pairTyping],
      row Examples.MLTT.typingRow ``Examples.MLTT.typingRow "mltt.sigma-typing" "MLTT"
        s!"⊢ {pairText} : {sigmaText}" mlttScope
        [("context", "mltt.context"), ("term", "mltt.pair"), ("type", "mltt.sigma")] [] [sigmaForm, pairTyping],
      row Examples.MLTT.firstProjection ``Examples.MLTT.firstProjection "mltt.sigma-first" "MLTT"
        s!"⊢ fst {pairText} ≡ zero : ℕ" mlttScope
        [("context", "mltt.context"), ("term", "mltt.first"), ("type", "mltt.nat")] []
        [step Examples.MLTT.firstProjection ``Examples.MLTT.firstProjection "fst" "first projection beta"
          s!"⊢ fst {pairText} ≡ zero : ℕ"],
      row Examples.MLTT.secondProjection ``Examples.MLTT.secondProjection "mltt.sigma-second" "MLTT"
        s!"⊢ snd {pairText} ≡ refl zero : Id ℕ zero zero" mlttScope
        [("context", "mltt.context"), ("term", "mltt.second"), ("type", "mltt.zero-fiber")] []
        [step Examples.MLTT.secondProjection ``Examples.MLTT.secondProjection "snd" "second projection beta"
          s!"⊢ snd {pairText} ≡ refl zero : Id ℕ zero zero"]])] ++
    (if withInterpretations then [("claimIndex", claimIndex)] else [])

end NamedLogicExport

public def main (args : List String) : IO Unit := do
  match args with
  | [revision] => IO.println (NamedLogicExport.plan revision).compress
  | [revision, "--interpretations"] => IO.println (NamedLogicExport.plan revision true).compress
  | _ => throw (IO.userError "expected the Git revision of the example sources and optional --interpretations")
