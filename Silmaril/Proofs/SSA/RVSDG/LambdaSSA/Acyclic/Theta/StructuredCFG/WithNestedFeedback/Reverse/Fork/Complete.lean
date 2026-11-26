module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.NestedFeedback.Reverse.Thms

/-! # Completeness for one nested-feedback arm and a shared structured tail -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Proofs

open Sequential
open Sequential.Flat.Serial (Code WirePorts)
open NestedFeedback.Reverse (Key readTheta readOuterWith)
open Flat.Numbered.Recognize (opcodeKey instructionKey effectKey)
open OrderedRuntime.Structured (primitiveNode gammaNode)
open NestedTheta (Node)
open NestedTheta.ExplicitRuntime (thetaNode)
open NestedTheta.ExplicitRuntime.Splice (append relocate changeLive)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq τ]
variable {A X Z U M Y B K I J L E D : τ}
variable {ps ts : List (Ports (OrderedRuntime.Structured.Ty τ))}

abbrev shape (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts) :
    Syntax Φ A X Z L E D (Selection M Y I J ++ ts) :=
  .branch gate (.structured p.toSyntax) (.nested q) (.structured k.toSyntax)

private def keys (q : NestedFeedback.Loop Φ Y B K M) : Key τ Φ × Key τ Φ × Key τ Φ :=
  (.enter Y B K M q.enter.op, .inner B K q.inner.op, .finish Y B K M q.finish.op)

private def leftScope (labels : StructuredCFG.Reverse.Layout τ Φ) : Scope τ Φ :=
  (WirePorts M M M :: (ps ++ [WirePorts M I J]),
    .atom (.cut Y M M M) :: (labels ++ [.atom (.cut U M I J)]))

omit [DecidableEq τ] in
private theorem read_left (p : Code Φ M M M U M M ps) (labels : StructuredCFG.Reverse.Layout τ Φ)
    (h : StructuredCFG.Reverse.scan p.1 = some labels) :
    suffixLayout (StructuredCFG.Wiring.leftArm (Y := Y) (I := I) (J := J) p).1 =
      some (leftScope (ps := ps) (Y := Y) (M := M) (U := U) (I := I) (J := J) labels) := by
  have first : StructuredCFG.Reverse.scan
      (Flat.Numbered.connector (Φ := Φ) (I := Y) (M := M) (E := M) (D := M)).1 =
        some [.atom (.cut Y M M M)] := rfl
  have last : StructuredCFG.Reverse.scan
      (Flat.Numbered.connector (Φ := Φ) (I := U) (M := M) (E := I) (D := J)).1 =
        some [.atom (.cut U M I J)] := rfl
  simp [suffixLayout, StructuredCFG.Wiring.leftArm, StructuredCFG.Reverse.scan_append, first, last, h, leftScope]

private theorem read_right (q : NestedFeedback.Loop Φ Y B K M) :
    readTerm (StructuredCFG.Wiring.rightArm (I := I) (J := J) (Leaf.code q)).1 =
      some ⟨Y, M, I, J, keys q, [], []⟩ := by
  simp only [StructuredCFG.Wiring.rightArm, Leaf.code, Leaf.bridge, Leaf.liftChecked,
    NestedFeedback.Wiring.loop, append, relocate, changeLive, Node.ofBase, primitiveNode, thetaNode,
    Leaf.Sigs, List.cons_append, List.nil_append, Flat.Numbered.connector, readTerm]
  simp only [enterTypes, exitTypes, linkTypes, readOpcode, opcodeKey, instructionKey, effectKey,
    Option.bind_some, readTheta, readOuterWith, readNested, Leaf.liftInstruction,
    NestedFeedback.Wiring.outerBody, NestedFeedback.Wiring.innerBody, Leaf.liftChecked,
    NestedFeedback.Wiring.returnStep, Node.ofBase, primitiveNode, thetaNode,
    NestedFeedback.Reverse.effectKey, NestedFeedback.Reverse.readInnerWith, suffixLayout, keys]
  simp [StructuredCFG.Reverse.scan]

private theorem read_generated (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts)
    {left tail : StructuredCFG.Reverse.Layout τ Φ}
    (hp : StructuredCFG.Reverse.scan p.toSyntax.code.1 = some left)
    (hk : StructuredCFG.Reverse.scan k.toSyntax.code.1 = some tail) :
    read (shape (X := X) (Z := Z) gate p q k).graph =
      some ⟨.classifier gate, leftScope (ps := ps) (U := U) (M := M) (Y := Y) (I := I) (J := J) left,
        ⟨Y, M, I, J, keys q, [], []⟩, (ts, tail)⟩ := by
  simp only [read, Syntax.graph, NestedTheta.Term.toTerm_toGraph]
  simp only [Syntax.code, StructuredCFG.Wiring.branch, StructuredCFG.Wiring.select, append, readFork,
    Selection, List.cons_append, List.nil_append, Node.ofBase, primitiveNode, gammaNode, changeLive]
  simp only [Wires.Reverse.readKind, ExplicitRuntime.Reverse.primitive, readArms, Fin.cases_zero, read_left _ _ hp]
  simp [suffixLayout, StructuredCFG.Reverse.scan_relocate, hk]
  change (((readTerm (StructuredCFG.Wiring.rightArm (I := I) (J := J) (Leaf.code q)).1).bind _).bind _) = _
  rw [read_right]
  rfl

theorem candidate_generated (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts)
    (pl : StructuredCFG.Reverse.Supported p) (kl : StructuredCFG.Reverse.Supported k) :
    candidate (shape (X := X) (Z := Z) gate p q k).graph = some (shape gate p q k) := by
  have left := StructuredCFG.Reverse.candidate_generated p pl
  have tail := StructuredCFG.Reverse.candidate_generated k kl
  simp only [StructuredCFG.Reverse.candidate, StructuredCFG.Syntax.graph, NestedTheta.Term.toTerm_toGraph] at left tail
  cases lp : StructuredCFG.Reverse.scan p.toSyntax.code.1 with
  | none => simp [lp] at left
  | some leftLabels =>
    have decodedLeft : StructuredCFG.Reverse.decodeLayout leftLabels = some p := by simpa [lp] using left
    cases kp : StructuredCFG.Reverse.scan k.toSyntax.code.1 with
    | none => simp [kp] at tail
    | some tailLabels =>
      have decodedTail : StructuredCFG.Reverse.decodeLayout tailLabels = some k := by simpa [kp] using tail
      have nested : NestedFeedback.Reverse.decode (keys q) = some ⟨B,K,q⟩ :=
        NestedFeedback.Reverse.decode_generated q
      rw [candidate, read_generated gate p q k lp kp]
      simp [decode, leftScope, StructuredCFG.Reverse.splitArm, List.reverse_append, decodedTail, nested, shape]
      rw [List.dropLast_concat, decodedLeft]
      rfl

variable [DecidableEq Φ]

theorem recover_generated (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts)
    (pl : StructuredCFG.Reverse.Supported p) (kl : StructuredCFG.Reverse.Supported k) :
    let s := shape (X := X) (Z := Z) gate p q k
    recover s.graph = some ⟨s.source.region, .generated s⟩ := by
  simp [recover, candidate_generated gate p q k pl kl, certify, Decomposition.raise]

theorem recover_canonical (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : StructuredCFG.Reverse.Normal Φ M M M U M M ps) (q : NestedFeedback.Loop Φ Y B K M)
    (k : StructuredCFG.Reverse.Normal Φ M I J L E D ts) :
    (recover (shape (X := X) (Z := Z) gate p q k).graph).isSome = true := by
  obtain ⟨p', hp, cp⟩ := StructuredCFG.Reverse.associate_bodies p
  obtain ⟨k', hk, ck⟩ := StructuredCFG.Reverse.associate_bodies k
  have same : (shape (X := X) (Z := Z) gate p' q k').graph =
      (shape (X := X) (Z := Z) gate p q k).graph := by
    simp only [Syntax.graph, Syntax.code, cp, ck]
  rw [← same, recover_generated gate p' q k' hp hk]
  rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Fork.Proofs
