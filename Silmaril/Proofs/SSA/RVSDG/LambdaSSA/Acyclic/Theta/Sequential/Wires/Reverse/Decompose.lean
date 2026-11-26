module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # Generated two-loop graphs have a source-free decomposition -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Proofs

open OrderedTheta (carried carriedData)
open OrderedRuntime.Structured (Data Threaded runtime)
open NestedTheta.ExplicitRuntime (Checked)
open TwoBlock.TwoExit (Pure)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K M C J E D : τ}

private theorem collect_some {α : Type u} (xs : List α) :
    (xs.map some).mapM (m := Option) id = some xs := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, List.mapM_cons, id_eq, ih]; rfl

private theorem collect_ofFn {α : Type u} {n : Nat} (f : Fin n → α) :
    (List.ofFn fun i => some (f i)).mapM (m := Option) id = some (List.ofFn f) :=
  (congrArg (fun xs : List (Option α) => xs.mapM (m := Option) id)
    (@List.map_ofFn _ _ _ f some).symm).trans (collect_some (List.ofFn f))

theorem read_lift {args outs : Ports (OrderedRuntime.Structured.Ty τ)}
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}
    {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : NestedTheta.Term (ExplicitRuntime.Op Φ) (Threaded args) past sigs (Threaded outs)}
    (check : Checked (Pure τ) (ExplicitRuntime.Effect Φ) a b live t) :
    readBody (liftChecked check).1 = some (ExplicitRuntime.Reverse.read t) := by
  induction check with
  | ret => rfl
  | primitive live i o op wires checked tail =>
    cases op <;> simp only [liftChecked, liftInstruction, readBody, readKind, NestedTheta.Node.ofBase,
      OrderedRuntime.Structured.primitiveNode, ExplicitRuntime.Reverse.read,
      ExplicitRuntime.Reverse.vertex, tail] <;> rfl
  | gamma extra selector live i o wires sigs checked rest inner outer =>
    simp only [liftChecked, readBody, readKind, NestedTheta.Node.ofBase,
      OrderedRuntime.Structured.gammaNode, ExplicitRuntime.Reverse.read,
      ExplicitRuntime.Reverse.vertex, inner, outer]
    rw [collect_ofFn]
    rfl
  | theta live i wires sigs checked rest inner outer =>
    simp only [liftChecked, readBody, readKind, NestedTheta.ExplicitRuntime.thetaNode,
      ExplicitRuntime.Reverse.read, ExplicitRuntime.Reverse.vertex, inner, outer]
    rfl

private abbrev bodyLabels (s : Loop Φ A B K E D) :=
  ExplicitRuntime.Reverse.read (ExplicitRuntime.Wiring.thetaBody s).2.1

private theorem single_labels (s : Loop Φ A B K E D) :
    ExplicitRuntime.Reverse.read (ExplicitRuntime.graph s).toTerm = [.theta (bodyLabels s)] := by
  rw [ExplicitRuntime.graph, NestedTheta.Term.toTerm_toGraph]
  rfl

private noncomputable def singleView (s : Loop Φ A B K E D) :
    ExplicitRuntime.Reverse.LoopView Φ [.theta (bodyLabels s)] A B K E D :=
  single_labels s ▸ (ExplicitRuntime.Reverse.canonical s).view

private theorem decode_cast {xs ys : List (Vertex (τ := τ) (Φ := Φ))} (h : xs = ys)
    (w : ExplicitRuntime.Reverse.LoopView Φ xs A B K E D) :
    (h ▸ w : ExplicitRuntime.Reverse.LoopView Φ ys A B K E D).decode = w.decode := by
  cases h
  rfl

private theorem singleView_decode (s : Loop Φ A B K E D) : (singleView s).decode = s := by
  rw [singleView, decode_cast]
  exact ExplicitRuntime.Reverse.canonical_decode s

private theorem read_graph (s : Loops Φ A B K M C J E D) :
    read (graph s).toTerm = some (bodyLabels s.first, bodyLabels s.second) := by
  rw [graph, NestedTheta.Term.toTerm_toGraph]
  change
    (do
      let xs ← readBody (liftChecked (ExplicitRuntime.Wiring.thetaBody s.first).2.2).1
      let ys ← readBody (liftChecked (ExplicitRuntime.Wiring.thetaBody s.second).2.2).1
      pure (xs, ys)) = _
  rw [read_lift, read_lift]
  rfl

private noncomputable def view (s : Loops Φ A B K M C J E D) :
    View Φ A B K M C J E D (bodyLabels s.first, bodyLabels s.second) :=
  ⟨singleView s.first, singleView s.second⟩

private theorem view_decode (s : Loops Φ A B K M C J E D) : (view s).decode = s := by
  change (⟨(singleView s.first).decode, (singleView s.second).decode⟩ : Loops Φ A B K M C J E D) = s
  rw [singleView_decode, singleView_decode]

noncomputable def canonical (s : Loops Φ A B K M C J E D) : Decomposition (graph s) B K C J :=
  ⟨graphChecked s, (bodyLabels s.first, bodyLabels s.second), read_graph s, view s, congrArg graph (view_decode s)⟩

theorem raise_canonical (s : Loops Φ A B K M C J E D) : (raise (canonical s)).1 = region s :=
  congrArg region (view_decode s)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Wires.Reverse.Proofs
