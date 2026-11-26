module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Numbered.Recognize.Structured.Thms
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Scan

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Proofs

open Sequential
open Sequential.Flat.Numbered.Recognize (parse_thetaBody loop_associated)
open Sequential.Flat.Serial.Recognize (Output)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K X Z L E D : τ}
variable {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

private theorem weight_append (p q : Layout τ Φ) : weight (p ++ q) = weight p + weight q := by
  induction p with
  | nil => simp [weight]
  | cons head tail ih =>
    cases head <;> simp only [List.cons_append, weight, ih] <;> omega

private theorem split_snoc (p : Layout τ Φ) (h m i j : τ) :
    splitArm (p ++ [.atom (.cut h m i j)]) = some (⟨h,i,j⟩, p) := by
  simp [splitArm, List.reverse_append]

private theorem loop_code_eq {s t : Loop Φ A B K E D}
    (same : ExplicitRuntime.Wiring.loop s = ExplicitRuntime.Wiring.loop t) :
    (Syntax.loop s).code = (Syntax.loop t).code := by
  change Wires.liftChecked (ExplicitRuntime.Wiring.loop s).2 =
    Wires.liftChecked (ExplicitRuntime.Wiring.loop t).2
  rw [same]

/-- Body association affects source sequencing syntax but preserves each
loop's checked emission. The structured constructors reuse the same codes. -/
theorem associate_bodies (n : Normal Φ A X Z L E D sigs) :
    ∃ out : Normal Φ A X Z L E D sigs, Supported out ∧ out.toSyntax.code = n.toSyntax.code := by
  induction n with
  | loop s =>
    obtain ⟨s', hs, same⟩ := loop_associated s
    exact ⟨.loop s', hs, loop_code_eq same⟩
  | link s rest ih =>
    obtain ⟨s', hs, same⟩ := loop_associated s
    obtain ⟨rest', hrest, tail⟩ := ih
    refine ⟨.link s' rest', ⟨hs,hrest⟩, ?_⟩
    simp only [Normal.toSyntax, Syntax.code]
    rw [show (Flat.Serial.Spine.loop s').code = (Flat.Serial.Spine.loop s).code from loop_code_eq same,
      tail]
  | branch gate left right tail hl hr ht =>
    obtain ⟨left', sl, l⟩ := hl
    obtain ⟨right', sr, r⟩ := hr
    obtain ⟨tail', st, t⟩ := ht
    refine ⟨.branch gate left' right' tail', ⟨sl,sr,st⟩, ?_⟩
    simp only [Normal.toSyntax, Syntax.code]
    rw [l, r, t]


variable [DecidableEq τ]

private theorem parse_emitted (n : Normal Φ A X Z L E D sigs) (h : Supported n)
    (fuel : Nat) (enough : weight (emitted n) ≤ fuel) :
    parse fuel A X Z (emitted n) = some (pack n) := by
  induction n generalizing fuel with
  | loop s =>
    cases fuel with
    | zero => simp [emitted, loopEntry, weight] at enough
    | succ fuel => simp [emitted, loopEntry, parse, parse_thetaBody s h]
  | link s k ih =>
    obtain ⟨head, tail⟩ := h
    cases fuel with
    | zero => simp [emitted, loopEntry, weight] at enough
    | succ fuel =>
      have bounded : weight (emitted k) ≤ fuel := by
        simp only [emitted, loopEntry, cutEntry, weight] at enough
        omega
      simp [emitted, loopEntry, cutEntry, parse, parse_thetaBody s head, ih tail fuel bounded, pack]
  | branch gate p q k hp hq hk =>
    obtain ⟨left, right, tail⟩ := h
    cases fuel with
    | zero => simp [emitted, weight] at enough
    | succ fuel =>
      simp only [emitted, cutEntry, weight, weight_append] at enough
      have lp : weight (emitted p) ≤ fuel := by omega
      have rq : weight (emitted q) ≤ fuel := by omega
      have tk : weight (emitted k) ≤ fuel := by omega
      simp [emitted, parse, cutEntry, split_snoc, hp left fuel lp,
        hq right fuel rq, hk tail fuel tk, expect, pack]

theorem candidate_generated (n : Normal Φ A X Z L E D sigs) (h : Supported n) :
    candidate n.toSyntax.graph = some n := by
  simp only [candidate, Syntax.graph, NestedTheta.Term.toTerm_toGraph, scan_emitted]
  have parsed := parse_emitted n h (weight (emitted n)) (Nat.le_refl _)
  change (do
    let ⟨out, shape⟩ ← parse (weight (emitted n)) A X Z (emitted n)
    if eq : out = (⟨L,E,D,sigs⟩ : Output τ) then
      some (Eq.mp (congrArg (fun ix => Normal Φ A X Z ix.carry ix.left ix.right ix.sigs) eq) shape)
    else none) = some n
  rw [parsed]
  simp [pack]

variable [DecidableEq Φ]

theorem recover_isSome_iff (g : Flat.Serial.Graph Φ A X Z L E D sigs) :
    (recover g).isSome = true ↔ ∃ n : Normal Φ A X Z L E D sigs, n.toSyntax.graph = g := by
  constructor
  · intro accepted
    cases h : recognize g with
    | none => simp [recover, h] at accepted
    | some m => exact ⟨m.view, m.wiring⟩
  · rintro ⟨n, rfl⟩
    obtain ⟨out, supported, code⟩ := associate_bodies n
    have same : out.toSyntax.graph = n.toSyntax.graph := congrArg (fun c => c.1.toGraph) code
    rw [← same]
    simp [recover, recognize, candidate_generated out supported, certify]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.Reverse.Proofs
