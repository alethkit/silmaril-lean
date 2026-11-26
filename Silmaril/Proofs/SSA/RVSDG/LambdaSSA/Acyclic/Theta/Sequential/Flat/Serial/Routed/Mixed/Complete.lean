module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs

open StructuredCFG.WithNestedFeedback.Reverse.Recursive
  (Entry Layout decodeLayout expect pack parse scan scan_append scan_parse_generated weight)
open NestedTheta (Node)
open OrderedRuntime.Structured (gammaNode primitiveNode)
open Numbered.Recognize (opcodeKey instructionKey effectKey)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A E M D H : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem scan_select (q : Code Φ M E D M E D qs) (arm : Layout τ Φ)
    (hq : scan q.1 = some arm) :
    scan (select (H := H) q).1 = some [.route H E M D, .fork [] arm] := by
  simp only [select, scan, Node.ofBase, primitiveNode, gammaNode,
    StructuredCFG.WithNestedFeedback.Reverse.Recursive.readEntry,
    StructuredCFG.WithNestedFeedback.Reverse.readOpcode, opcodeKey, instructionKey, effectKey,
    Fin.cases_zero]
  change (do
    let marker ← some (Entry.route H E M D)
    let tail ← (do
      let branch ← (do
        let left ← some []
        let right ← scan q.1
        pure (Entry.fork left right))
      let suffix ← some []
      pure (branch :: suffix))
    pure (marker :: tail)) = _
  rw [hq]
  rfl

theorem candidate_generated [DecidableEq τ] (s : Components Φ A E M D ps) (h : s.Supported) :
    candidate s.graph = some s := by
  obtain ⟨producerLabels, scannedProducer, parsedProducer⟩ := scan_parse_generated s.producer h.1
  obtain ⟨arm, scannedConsumer, parsedConsumer⟩ := scan_parse_generated s.consumer h.2
  have scanned : scan s.graph.toTerm = some (producerLabels ++ [.route s.H E M D, .fork [] arm]) := by
    simp only [Components.graph, Components.code, splice, NestedTheta.Term.toTerm_toGraph,
      scan_append, scannedProducer, scan_select _ _ scannedConsumer]
    rfl
  have cut : splitLayout E M D (producerLabels ++ [.route s.H E M D, .fork [] arm]) =
      some (s.H, producerLabels, arm) := by
    simp [splitLayout, List.reverse_append]
  have decoded : decodeLayout producerLabels = some s.producer := by
    simp [decodeLayout, parsedProducer, pack]
  rw [candidate, scanned, Option.bind_some, cut]
  change (do
    let producer ← decodeLayout producerLabels
    let parsed ← parse (weight arm) M E D arm
    let ⟨rows, consumer⟩ ← expect parsed M E D
    return (⟨s.H, producer, rows, consumer⟩ : Components Φ A E M D ps)) = _
  cases s
  simp [decoded, parsedConsumer, expect, pack]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Routed.Mixed.Proofs
