module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms

/-! # Read the relocated suffix and recover the canonical mixed emission -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Proofs

open Sequential
open Sequential.Flat.Serial (Joined)
open NestedFeedback.Reverse (Key readTheta readOuterWith)
open Flat.Numbered.Recognize (opcodeKey instructionKey effectKey)
open OrderedRuntime.Structured (primitiveNode)
open NestedTheta (Term Node)
open NestedTheta.ExplicitRuntime (thetaNode)
open NestedTheta.ExplicitRuntime.Splice (append relocate changeLive)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ]
variable {A B K M I J L E D : τ}
variable {qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev joined (s : NestedFeedback.Loop Φ A B K M) (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) :
    Syntax Φ A M M L E D (Joined M I J (Leaf.Sigs A M) qs) :=
  .link (.nested s) (.structured n.toSyntax)

def keys (s : NestedFeedback.Loop Φ A B K M) : Key τ Φ × Key τ Φ × Key τ Φ :=
  (.enter A B K M s.enter.op, .inner B K s.inner.op, .finish A B K M s.finish.op)

private theorem read_generated (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) :
    read (joined s n).graph =
      (StructuredCFG.Reverse.scan n.toSyntax.code.1).map fun labels => ⟨A, M, I, J, keys s, qs, labels⟩ := by
  simp only [read, Syntax.graph, NestedTheta.Term.toTerm_toGraph]
  simp only [Syntax.code, Flat.Serial.splice, Leaf.code, Leaf.bridge, Leaf.liftChecked,
    NestedFeedback.Wiring.loop, append, relocate, changeLive, Node.ofBase, primitiveNode, thetaNode,
    Leaf.Sigs, List.cons_append, List.nil_append, Flat.Numbered.connector, readTerm]
  simp only [enterTypes, exitTypes, linkTypes, readOpcode, opcodeKey, instructionKey, effectKey,
    Option.bind_some, readTheta, readOuterWith, readNested, Leaf.liftInstruction,
    NestedFeedback.Wiring.outerBody, NestedFeedback.Wiring.innerBody, Leaf.liftChecked,
    NestedFeedback.Wiring.returnStep, Node.ofBase, primitiveNode, thetaNode,
    NestedFeedback.Reverse.effectKey, NestedFeedback.Reverse.readInnerWith, suffixLayout,
    StructuredCFG.Reverse.scan_relocate, keys]
  cases StructuredCFG.Reverse.scan n.toSyntax.code.1 <;> simp

theorem candidate_generated (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) (supported : StructuredCFG.Reverse.Supported n) :
    candidate (joined s n).graph = some (joined s n) := by
  have nested : NestedFeedback.Reverse.decode (keys s) = some ⟨B, K, s⟩ :=
    NestedFeedback.Reverse.decode_generated s
  have tail := StructuredCFG.Reverse.candidate_generated n supported
  simp only [StructuredCFG.Reverse.candidate, StructuredCFG.Syntax.graph, NestedTheta.Term.toTerm_toGraph] at tail
  rw [candidate, read_generated]
  cases layout : StructuredCFG.Reverse.scan n.toSyntax.code.1 with
  | none => simp [layout] at tail
  | some labels =>
    have decoded : StructuredCFG.Reverse.decodeLayout labels = some n := by simpa [layout] using tail
    simp [decode, nested, decoded, joined]

variable [DecidableEq Φ]

theorem recover_generated (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) (supported : StructuredCFG.Reverse.Supported n) :
    recover (joined s n).graph = some ⟨(joined s n).source.region, .generated (joined s n)⟩ := by
  simp [recover, candidate_generated s n supported, certify, Decomposition.raise]

theorem recover_canonical (s : NestedFeedback.Loop Φ A B K M)
    (n : StructuredCFG.Reverse.Normal Φ M I J L E D qs) :
    (recover (joined s n).graph).isSome = true := by
  obtain ⟨out, supported, same⟩ := StructuredCFG.Reverse.associate_bodies n
  have graph_eq : (joined s out).graph = (joined s n).graph :=
    congrArg (fun code => (Flat.Serial.splice (Leaf.code s) code).1.toGraph) same
  rw [← graph_eq, recover_generated s out supported]
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Proofs
