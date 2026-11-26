module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Thms
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Scan

/-! # Completeness on the emitted serial layout -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Proofs

open Numbered.Recognize (RightAssociated parse_thetaBody)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A X Y H M I J L E D B K : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private def marks : {A X Y L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Spine Φ A X Y L E D sigs → List (Mark τ Φ)
  | _, _, _, _, _, _, _, .loop s => [leafMark s]
  | _, _, _, _, _, _, _, .link (H := h) (M := m) (I := i) (J := j) p q =>
    marks p ++ .cut h m i j :: marks q

private theorem scan_spine (s : Spine Φ A X Y L E D sigs) : scan s.code.1 = some (marks s) := by
  induction s with
  | loop s => exact scan_leaf s
  | link p q hp hq =>
    rw [scan_link, hp, hq]
    rfl

variable [DecidableEq τ]

private theorem extend_leaf (p : Spine Φ A X Y H M M sigs) (q : Loop Φ M B K E D)
    (h : RightAssociated q.body) (suffix : List (Mark τ Φ)) :
    extend (pack p) (Mark.cut H M E D :: leafMark q :: suffix) = extend (pack (.link p (.loop q))) suffix := by
  simp [leafMark, pack, extend, parse_thetaBody q h]

/-- Keeping the unread suffix explicit lets the proof follow the left fold,
with a single parser call per θ. -/
private theorem parse_marks (s : Spine Φ A X Y L E D sigs) (h : LeftAssociated s) (suffix : List (Mark τ Φ)) :
    parse (marks s ++ suffix) = extend (pack s) suffix := by
  induction h generalizing suffix with
  | single s h =>
    simp only [marks, leafMark, List.cons_append, List.nil_append, parse, parse_thetaBody s h]
    rfl
  | push next first h ih =>
    simp only [marks, List.append_assoc, List.cons_append, List.nil_append]
    rw [ih, extend_leaf _ next h]

theorem candidate_generated (s : Spine Φ A X Y L E D sigs) (h : LeftAssociated s) :
    candidate s.graph = some s := by
  simp only [candidate, Spine.graph, NestedTheta.Term.toTerm_toGraph, scan_spine]
  have parsed : parse (marks s) = some (pack s) := by
    simpa only [List.append_nil, extend] using parse_marks s h []
  change (do
    let ⟨o, t⟩ ← parse (marks s)
    if same : o = (⟨L, E, D, sigs⟩ : Output τ) then
      some (Eq.mp (congrArg (fun ix => Spine Φ A X Y ix.carry ix.left ix.right ix.sigs) same) t)
    else none) = some s
  rw [parsed]
  simp [pack]

variable [DecidableEq Φ]

private theorem certify_generated (s : Spine Φ A X Y L E D sigs) :
    certify s.graph s = some s.decomposition := by
  cases s with
  | loop s => simp [certify, Spine.decomposition]
  | link p q =>
    have cut : Cut p.code q.code (Spine.link p q).graph := ⟨rfl⟩
    simp only [certify, cut.certified, Option.map_some, Spine.decomposition]

theorem complete (s : Spine Φ A X Y L E D sigs) (h : LeftAssociated s) :
    recognize s.graph = some s.decomposition := by
  simp only [recognize, candidate_generated s h, Option.bind_some, certify_generated]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Serial.Recognize.Proofs
