module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Proofs

open Sequential
open Sequential.Flat.Serial (Code)
open Sequential.Flat.Serial.Recognize (mark connectorMark)
open Sequential.Flat.Numbered.Recognize (budget)
open Sequential.Wires.Reverse (readBody_lift)
open NestedTheta.ExplicitRuntime (Checked EntryChecked thetaNode)
open NestedTheta.ExplicitRuntime.Splice (Routing relocate append)
open OrderedRuntime.Structured (Data Threaded runtime primitiveNode gammaNode)
open TwoBlock.TwoExit (Pure)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {args input outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past sigs target after : List (Ports (OrderedRuntime.Structured.Ty τ))}

theorem scan_relocate {a : Data input} {b : Data outs} {c : Data args}
    {live : Origin (Threaded input) past runtime}
    {t : NestedTheta.Term (Wires.Op Φ) (Threaded input) past sigs (Threaded outs)}
    (route : Routing (Threaded input) past (Threaded args) target)
    (h : Checked (Pure τ) (Wires.Effect Φ) a b live t) :
    scan (relocate (c := c) route h).1 = scan t := by
  induction h generalizing args target with
  | ret => rfl
  | primitive live i o op wires rest ih =>
    simp only [relocate, scan, ih, NestedTheta.Node.ofBase, primitiveNode]
  | gamma extra selector live i o xs sigs arms rest ihArms ihRest =>
    simp only [relocate, scan, ihRest, NestedTheta.Node.ofBase, gammaNode]
  | theta live i wires sigs body rest ihBody ihRest =>
    simp only [relocate, scan, ihRest, thetaNode]

private theorem cons_append (head : Option (Entry τ Φ)) (rest tail : Option (Layout τ Φ)) :
    (do let h ← head; let suffix ← (do let xs ← rest; let ys ← tail; pure (xs ++ ys)); pure (h :: suffix)) =
      (do let xs ← (do let h ← head; pure (h :: (← rest))); let ys ← tail; pure (xs ++ ys)) := by
  cases head <;> cases rest <;> cases tail <;> rfl

theorem scan_append {a : Data args} {b : Data input} {c : Data outs}
    {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Wires.Op Φ) (Threaded args) past sigs (Threaded input)}
    {q : NestedTheta.Term (Wires.Op Φ) (Threaded input) [] after (Threaded outs)}
    (first : Checked (Pure τ) (Wires.Effect Φ) a b live p) (next : EntryChecked (a := b) (b := c) q) :
    scan (append next first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) := by
  induction first with
  | ret =>
    simp only [append, scan_relocate, scan]
    cases scan q <;> rfl
  | primitive live i o op wires rest ih =>
    simp only [append, scan, NestedTheta.Node.ofBase, primitiveNode, ih]
    exact cons_append _ _ _
  | gamma extra selector live i o xs sigs arms rest ihArms ihRest =>
    simp only [append, scan, NestedTheta.Node.ofBase, gammaNode, ihRest]
    exact cons_append _ _ _
  | theta live i wires sigs body rest ihBody ihRest =>
    simp only [append, scan, thetaNode, ihRest]
    exact cons_append _ _ _

variable {A B K X Z M Y I J U V L E D : τ}
variable {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))}

@[expose] def loopEntry (s : Loop Φ A B K E D) : Entry τ Φ :=
  let body := ExplicitRuntime.Wiring.thetaBody s
  .atom (.loop (budget (Wires.liftChecked body.2.2).1) [.theta (ExplicitRuntime.Reverse.read body.2.1)])

@[expose] def cutEntry (h m e d : τ) : Entry τ Φ := .atom (.cut h m e d)

private theorem scan_loop (s : Loop Φ A B K E D) :
    scan (Flat.Serial.Spine.loop s).code.1 = some [loopEntry s] := by
  simp only [Flat.Serial.Spine.code, ExplicitRuntime.Wiring.loop, Wires.liftChecked, scan,
    readEntry, mark, thetaNode, readBody_lift]
  rfl

private theorem scan_cut :
    scan (Flat.Numbered.connector (Φ := Φ) (I := U) (M := M) (E := I) (D := J)).1 =
      some [cutEntry U M I J] := rfl

@[expose] def emitted : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D sigs → Layout τ Φ
  | _, _, _, _, _, _, _, .loop s => [loopEntry s]
  | _, _, _, _, _, _, _, .link (A := a) (M := m) (I := i) (J := j) s k =>
    loopEntry s :: cutEntry a m i j :: emitted k
  | _, _, _, _, _, _, _, .branch (U := u) (V := v) (M := m) (Y := y) (I := i) (J := j) gate p q k =>
    .classifier gate ::
      .fork (cutEntry y m m m :: (emitted p ++ [cutEntry u m i j]))
        (emitted q ++ [cutEntry v m i j]) :: emitted k

private theorem scan_select (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
    (p : Code Φ M M M U M M ps) (q : Code Φ Y M M V M M qs) (left right : Layout τ Φ)
    (hp : scan p.1 = some left) (hq : scan q.1 = some right) :
    scan (Wiring.select (X := X) (Z := Z) (I := I) (J := J) gate p q).1 =
      some [.classifier gate, .fork
        (cutEntry Y M M M :: (left ++ [cutEntry U M I J])) (right ++ [cutEntry V M I J])] := by
  simp only [Wiring.select, scan, NestedTheta.Node.ofBase, primitiveNode, gammaNode, readEntry,
    Wires.Reverse.readKind, ExplicitRuntime.Reverse.primitive, Fin.cases_zero]
  change (do
    let classifier ← some (Entry.classifier gate)
    let body ← (do
      let fork ← (do
        return Entry.fork (← scan (Wiring.leftArm (I := I) (J := J) p).1)
          (← scan (Wiring.rightArm (I := I) (J := J) q).1))
      let rest ← some []
      return fork :: rest)
    return classifier :: body) = _
  simp only [Wiring.leftArm, Wiring.rightArm, scan_append, scan_cut, hp, hq]
  rfl

theorem scan_emitted (n : Normal Φ A X Z L E D sigs) :
    scan n.toSyntax.code.1 = some (emitted n) := by
  induction n with
  | loop s => exact scan_loop s
  | link s k ih =>
    simp only [Normal.toSyntax, Syntax.code, Flat.Serial.splice, scan_append, scan_loop, scan_cut, ih, emitted]
    rfl
  | branch gate p q k hp hq hk =>
    simp only [Normal.toSyntax, Syntax.code, Wiring.branch, scan_append, hk, scan_select gate _ _ _ _ hp hq,
      emitted]
    rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Proofs
