module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Proofs

open Sequential.Wires.Reverse (readBody_lift readBody)
open Sequential.Flat.Serial.Recognize (Mark scan mark scan_append)
open Sequential.Flat.Numbered.Recognize (RightAssociated budget parse_thetaBody loop_associated)
open NestedTheta.ExplicitRuntime.Splice (append)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A M Y E D B K I : τ}

private def loopMark (s : Loop Φ A B K E D) : Mark τ Φ :=
  let body := ExplicitRuntime.Wiring.thetaBody s
  .loop (budget (Sequential.Wires.liftChecked body.2.2).1) [.theta (ExplicitRuntime.Reverse.read body.2.1)]

private def emitted (s : Diamond Φ A M Y E D) : Layout τ Φ :=
  ⟨.classifier s.gate, [.cut Y M M M, loopMark s.left, .cut M M E D],
    [loopMark s.right, .cut Y M E D], loopMark s.next⟩

private theorem scan_loop (s : Loop Φ A B K E D) :
    scan (Sequential.Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2).1 = some [loopMark s] := by
  simp only [ExplicitRuntime.Wiring.loop, Sequential.Wires.liftChecked, scan,
    NestedTheta.ExplicitRuntime.thetaNode, mark, readBody_lift]
  rfl

private theorem scan_connector :
    scan (Sequential.Flat.Numbered.connector (Φ := Φ) (I := I) (M := M) (E := E) (D := D)).1 =
      some [Mark.cut I M E D] := rfl

private theorem scan_left (s : Diamond Φ A M Y E D) :
    scan (Wiring.left s).1 = some [.cut Y M M M, loopMark s.left, .cut M M E D] := by
  simp only [Wiring.left, scan_append, scan_loop, scan_connector]
  rfl

private theorem scan_right (s : Diamond Φ A M Y E D) :
    scan (Wiring.right s).1 = some [loopMark s.right, .cut Y M E D] := by
  simp only [Wiring.right, scan_append, scan_loop, scan_connector]
  rfl

private theorem read_emitted (s : Diamond Φ A M Y E D) :
    read (graph s) = some (emitted s) := by
  unfold read graph
  rw [NestedTheta.Term.toTerm_toGraph]
  let body := ExplicitRuntime.Wiring.thetaBody s.next
  change (do
    let selector ← some (ExplicitRuntime.Reverse.Vertex.classifier s.gate)
    let (left, right) ← (do return ((← scan (Wiring.left s).1), (← scan (Wiring.right s).1)))
    let next ← (do
      let labels ← readBody (Sequential.Wires.liftChecked body.2.2).1
      return Mark.loop (budget (Sequential.Wires.liftChecked body.2.2).1) [.theta labels])
    return (⟨selector, left, right, next⟩ : Layout τ Φ)) = _
  rw [scan_left, scan_right, readBody_lift]
  rfl

variable [DecidableEq τ]

theorem candidate_generated (s : Diamond Φ A M Y E D)
    (left : RightAssociated s.left.body) (right : RightAssociated s.right.body)
    (tail : RightAssociated s.next.body) :
    candidate (graph s) = some s := by
  rw [candidate, read_emitted, Option.bind_some]
  cases s
  simp [emitted, decode, loopMark, parse_thetaBody _ left, parse_thetaBody _ right,
    parse_thetaBody _ tail]

variable [DecidableEq Φ]

theorem recognize_generated (s : Diamond Φ A M Y E D)
    (left : RightAssociated s.left.body) (right : RightAssociated s.right.body)
    (tail : RightAssociated s.next.body) :
    recognize (graph s) = some ⟨s, rfl⟩ := by
  simp [recognize, candidate_generated s left right tail, certify]

theorem complete_generated (s : Diamond Φ A M Y E D) : (recover (graph s)).isSome = true := by
  obtain ⟨left, hl, leftCode⟩ := loop_associated s.left
  obtain ⟨right, hr, rightCode⟩ := loop_associated s.right
  obtain ⟨next, hn, nextCode⟩ := loop_associated s.next
  let associated := { s with left := left, right := right, next := next }
  have same : graph associated = graph s := by
    simp only [associated, graph, Wiring.code, Wiring.select, Wiring.left, Wiring.right]
    revert leftCode rightCode nextCode
    generalize ExplicitRuntime.Wiring.loop left = newLeft, ExplicitRuntime.Wiring.loop s.left = oldLeft,
      ExplicitRuntime.Wiring.loop right = newRight, ExplicitRuntime.Wiring.loop s.right = oldRight,
      ExplicitRuntime.Wiring.loop next = newNext, ExplicitRuntime.Wiring.loop s.next = oldNext
    rintro rfl rfl rfl
    rfl
  rw [← same, recover, recognize_generated associated hl hr hn]
  rfl

theorem recover_isSome_iff (g : Graph Φ A M Y E D) :
    (recover g).isSome = true ↔ ∃ s : Diamond Φ A M Y E D, graph s = g := by
  constructor
  · intro accepted
    cases h : recognize g with
    | none => simp [recover, h] at accepted
    | some d => exact ⟨d.view, d.wiring⟩
  · rintro ⟨s, rfl⟩
    exact complete_generated s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.LoopDiamond.Reverse.Proofs
