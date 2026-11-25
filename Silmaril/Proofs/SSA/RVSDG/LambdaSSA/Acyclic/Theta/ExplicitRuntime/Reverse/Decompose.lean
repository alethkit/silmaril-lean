module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # The ordinary forward compiler supplies a structural parse -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Proofs

open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Data Threaded runtime runtimePort nextRuntime Instruction)
open TwoBlock.TwoExit (Carrier Pure)
open Wiring (Code Tail emit)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D S : τ}
variable {args ins out outs : Ports (OrderedRuntime.Structured.Ty τ)}
variable {past : List (Ports (OrderedRuntime.Structured.Ty τ))}
variable {a : Data args} {o : Data outs}
variable {live : Origin (Threaded args) past runtime}

private def bodyView : {A B : τ} → Body Φ A B → Σ xs, BodyView Φ xs A B
  | _, _, .instruction p => ⟨_, .call p⟩
  | _, _, .sequence l r => ⟨_, .sequence (bodyView l).2 (bodyView r).2⟩
  | _, _, .choice p l r => ⟨_, .gamma p (bodyView l).2 (bodyView r).2⟩

private theorem bodyView_decode (b : Body Φ A B) : (bodyView b).2.decode = b := by
  induction b <;> simp_all only [bodyView, BodyView.decode]

private theorem read_primitive (i : Data ins) (d : Data out) (op : Instruction (Pure τ) (Effect Φ) ins out)
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out)) :
    read (Wiring.primitive i d op live inputs rest).2.1 = primitive op :: read rest.2.1 := by
  rfl

private theorem read_choice (i : Data ins) (d : Data out)
    (l r : Code (past := []) Φ i d (.arg (runtimePort ins)))
    (selector : Origin (Threaded args) past (.control 2))
    (inputs : Wires (Threaded args) past ins) (rest : Code Φ a o (nextRuntime past out)) :
    read (Wiring.choice i d l r selector live inputs rest).2.1 =
      .gamma [read l.2.1, read r.2.1] :: read rest.2.1 := by
  simp only [Wiring.choice, read, vertex, NestedTheta.Node.ofBase, OrderedRuntime.Structured.gammaNode]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

private theorem read_finish (source : Origin (Threaded args) past (.value B)) :
    read (Wiring.finish (Φ := Φ) (a := a) past live source).2.1 = [] := by
  rfl

private theorem read_emit (b : Body Φ A B) (route : Input S A)
    (source : Origin (Threaded args) past (.value S)) (next : Tail Φ a o B)
    (suffix : List (Vertex τ Φ))
    (continuation : ∀ (future : List (Ports (OrderedRuntime.Structured.Ty τ)))
      (token : Origin (Threaded args) future runtime) (value : Origin (Threaded args) future (.value B)),
      read (next future token value).2.1 = suffix) :
    read (emit b route live source next).2.1 = (bodyView b).1 ++ suffix := by
  induction b generalizing args outs past S suffix with
  | instruction p =>
    simp only [emit, read_primitive, primitive, bodyView, continuation, List.cons_append, List.nil_append]
  | sequence l r ihL ihR =>
    simp only [emit, bodyView]
    rw [ihL _ _ _ ((bodyView r).1 ++ suffix) (fun _ _ _ => ihR _ _ _ _ continuation)]
    rw [List.append_assoc]
  | choice p l r ihL ihR =>
    simp only [emit, read_primitive, read_choice, primitive, bodyView, continuation,
      List.cons_append, List.nil_append]
    rw [ihL _ _ _ [] (fun _ _ _ => read_finish _), ihR _ _ _ [] (fun _ _ _ => read_finish _)]
    simp only [List.append_nil]

private theorem read_loop (s : Loop Φ A B K E D) :
    read (Wiring.loop s).1 =
      [.theta [.header s.header, .gamma [[.headerExit], (bodyView s.body).1 ++ [.join s.join]]]] := by
  change [Vertex.theta (read (Wiring.thetaBody s).2.1)] = _
  simp only [Wiring.thetaBody, read_primitive, read_choice, primitive, Wiring.exitArm]
  change [Vertex.theta [.header s.header, .gamma [[.headerExit], read (Wiring.bodyArm s).2.1]]] = _
  rw [Wiring.bodyArm, read_emit _ _ _ _ [.join s.join]]
  intro future token value
  rfl

private theorem read_graph (s : Loop Φ A B K E D) :
    read (graph s).toTerm =
      [.theta [.header s.header, .gamma [[.headerExit], (bodyView s.body).1 ++ [.join s.join]]]] := by
  rw [graph, NestedTheta.Term.toTerm_toGraph, read_loop]

private def loopView (s : Loop Φ A B K E D) : LoopView Φ (read (graph s).toTerm) A B K E D :=
  (read_graph s).symm ▸ LoopView.loop s.header (bodyView s.body).2 s.join

private theorem decode_cast {xs ys : List (Vertex τ Φ)} (h : xs = ys) (w : LoopView Φ xs A B K E D) :
    LoopView.decode (h ▸ w : LoopView Φ ys A B K E D) = w.decode := by
  cases h
  rfl

private theorem loopView_decode (s : Loop Φ A B K E D) : (loopView s).decode = s := by
  unfold loopView
  rw [decode_cast]
  change (⟨s.header, (bodyView s.body).2.decode, s.join⟩ : Loop Φ A B K E D) = s
  rw [bodyView_decode]

def canonical (s : Loop Φ A B K E D) : Decomposition (graph s) B K :=
  ⟨graphChecked s, loopView s, congrArg graph (loopView_decode s)⟩

theorem canonical_decode (s : Loop Φ A B K E D) : (canonical s).view.decode = s :=
  loopView_decode s

theorem raise_canonical_source (s : Loop Φ A B K E D) : (raise (canonical s)).1 = region s :=
  congrArg region (loopView_decode s)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Proofs
