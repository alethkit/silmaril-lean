module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms

/-! # Checked relocation preserves the serial scanner's marks -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Proofs

open OrderedRuntime.Structured (Data Threaded runtime)
open NestedTheta.ExplicitRuntime (Checked EntryChecked)
open NestedTheta.ExplicitRuntime.Splice (Routing relocate append)
open Wires.Reverse (readBody_lift)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {args input outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past target sigs after : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem scan_relocate {a : Data input} {b : Data outs} {c : Data args}
    {live : Origin (Threaded input) past runtime}
    {t : NestedTheta.Term (Wires.Op Φ) (Threaded input) past sigs (Threaded outs)}
    (f : Routing (Threaded input) past (Threaded args) target)
    (h : Checked (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) a b live t) :
    scan (relocate (c := c) f h).1 = scan t := by
  induction h generalizing args target with
  | ret => rfl
  | primitive live i o op wires rest ih =>
    simp only [relocate, scan, ih, NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode]
  | gamma => rfl
  | theta live i wires regions arms rest ihArms ihRest =>
    simp only [relocate, scan, ihRest, NestedTheta.ExplicitRuntime.thetaNode]

private theorem cons_append (head : Option (Mark τ Φ)) (rest tail : Option (List (Mark τ Φ))) :
    (do let h ← head; let suffix ← (do let xs ← rest; let ys ← tail; pure (xs ++ ys)); pure (h :: suffix)) =
      (do let xs ← (do let h ← head; pure (h :: (← rest))); let ys ← tail; pure (xs ++ ys)) := by
  cases head <;> cases rest <;> cases tail <;> rfl

theorem scan_append {a : Data args} {b : Data input} {c : Data outs}
    {live : Origin (Threaded args) past runtime}
    {p : NestedTheta.Term (Wires.Op Φ) (Threaded args) past sigs (Threaded input)}
    {q : NestedTheta.Term (Wires.Op Φ) (Threaded input) [] after (Threaded outs)}
    (first : Checked (TwoBlock.TwoExit.Pure τ) (Wires.Effect Φ) a b live p)
    (next : EntryChecked (a := b) (b := c) q) :
    scan (append next first).1 = (do let xs ← scan p; let ys ← scan q; pure (xs ++ ys)) := by
  induction first with
  | ret =>
    simp only [append, scan_relocate, scan]
    cases scan q <;> rfl
  | primitive live i o op wires rest ih =>
    simp only [append, scan, NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, ih]
    exact cons_append (τ := τ) (Φ := Φ) _ _ _
  | gamma => rfl
  | theta live i wires regions arms rest ihArms ihRest =>
    simp only [append, scan, NestedTheta.ExplicitRuntime.thetaNode, ihRest]
    exact cons_append (τ := τ) (Φ := Φ) _ _ _

variable {A X Y H M I J L E D B K : τ}
variable {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}

@[expose] def leafMark (s : Loop Φ A B K E D) : Mark τ Φ :=
  let code := ExplicitRuntime.Wiring.thetaBody s
  .loop (Numbered.Recognize.budget (Wires.liftChecked code.2.2).1)
    [.theta (ExplicitRuntime.Reverse.read code.2.1)]

theorem scan_leaf (s : Loop Φ A B K E D) :
    scan (Spine.loop s).code.1 = some [leafMark s] := by
  simp only [Spine.code, ExplicitRuntime.Wiring.loop, Wires.liftChecked, scan,
    NestedTheta.ExplicitRuntime.thetaNode, mark]
  rw [readBody_lift]
  rfl

theorem scan_link (p : Spine Φ A X Y H M M ps) (q : Spine Φ M I J L E D qs) :
    scan (Spine.link p q).code.1 =
      (do let xs ← scan p.code.1; let ys ← scan q.code.1; pure (xs ++ .cut H M I J :: ys)) := by
  simp only [Spine.code, splice, scan_append]
  have cut : scan (Numbered.connector (Φ := Φ) (I := H) (M := M) (E := I) (D := J)).1 =
      some [.cut H M I J] := rfl
  rw [cut]
  cases scan p.code.1 <;> cases scan q.code.1 <;> rfl

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Proofs
