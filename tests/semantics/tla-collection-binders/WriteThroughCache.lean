module

import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
meta import Silmaril.Logic.Temporal.TLA.DataElab.Collections.Defs
import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs
meta import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Check the original Coherence operator body in a standalone environment
with the four values it reads supplied by the caller. -/

open Silmaril.Logic.Temporal.TLA Resolution DataElab

private def fromResult {α ε : Type} [Repr ε] : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError (reprStr error))

public def main (args : List String) : IO Unit := do
  let [file] := args | throw (IO.userError "expected the pinned WriteThroughCache.tla path")
  let source ← fromResult (Surface.Parser.parseModule (← IO.FS.readFile file))
  unless source.name == "WriteThroughCache" &&
      source.extendsModules == ["Naturals", "Sequences", "MemoryInterface"] do
    throw (IO.userError "unexpected corpus module or imports")
  match Resolution.resolveWith .instanceSyntax [("pinned", .parsed source [])] "pinned" with
  | .error problem =>
    unless problem == ⟨⟨"pinned", [.import_ 0]⟩, .unresolvedImport "Naturals"⟩ do
      throw (IO.userError s!"unexpected whole-module diagnostic: {reprStr problem}")
  | .ok _ => throw (IO.userError "expected the intact module to require its EXTENDS inputs")
  let [unit] := source.units.filter (fun
    | .definition (.operator _ (.ident "Coherence" []) _) => true
    | _ => false)
    | throw (IO.userError "expected exactly one Coherence definition")
  let root := "coherence"
  let projected : Surface.Module := ⟨"CoherenceFixture", [],
    [.constants [(.ident "Proc" 0), (.ident "Adr" 0), (.ident "NoVal" 0)], .variables ["cache"], unit]⟩
  let registry ← fromResult (Resolution.resolve [(root, .parsed projected [])] root)
  let sourceSite : Site := ⟨root, [.unit 2]⟩
  let some defn := (registry.moduleAt root).bind (·.bindingAt (.ident "Coherence"))
    | throw (IO.userError "missing Coherence binding")
  let checked ← fromResult (Collections.lowerState registry [] (fun _ => none) 40 defn.id)
  let .bounded _ (.quant .forall) [([.name p, .name q], .rigid proc), ([.name a], .rigid adr)]
      (.logic .implies (.mem true (.rigid noVal) (.enum [left, right])) (.eq false lhs rhs)) := checked.term
    | throw (IO.userError s!"unexpected Coherence expansion: {reprStr checked.term}")
  let constantId := fun i => BindingId.declared ⟨root, [.unit 0, .member i]⟩
  let cache := BindingId.declared ⟨root, [.unit 1, .member 0]⟩
  let reads := fun term who => match term with
    | .index _ (.index _ (.flexible base) (.witness first)) (.witness second) =>
      base == cache && first == who && second == a
    | _ => false
  unless defn.id == .declared sourceSite && proc == constantId 0 && adr == constantId 1 &&
      noVal == constantId 2 && p != q && p != a && q != a &&
      reads left p && reads right q && reads lhs p && reads rhs q do
    throw (IO.userError "unexpected Coherence domains or witness uses")
  IO.println "WriteThroughCache.Coherence: shared Proc bound, separate Adr bound, and all four cache reads checked"
