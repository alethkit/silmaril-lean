module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Proofs

open ExplicitRuntime.Reverse (Vertex read)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A L B K E D : τ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

private theorem read_graph (s : Guarded Φ A L B K E D) :
    read (graph s).toTerm =
      [.classifier s.gate, .gamma [[], read (ExplicitRuntime.graph s.loop).toTerm]] := by
  rw [graph, ExplicitRuntime.graph, NestedTheta.Term.toTerm_toGraph, NestedTheta.Term.toTerm_toGraph]
  simp only [Wiring.code, Wiring.openCode, ExplicitRuntime.Wiring.primitive, ExplicitRuntime.Wiring.choice,
    ExplicitRuntime.Reverse.read, ExplicitRuntime.Reverse.vertex, ExplicitRuntime.Reverse.primitive,
    NestedTheta.Node.ofBase, OrderedRuntime.Structured.primitiveNode, OrderedRuntime.Structured.gammaNode]
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

private noncomputable def view (s : Guarded Φ A L B K E D) :
    View Φ (read (graph s).toTerm) A L B K E D :=
  (read_graph s).symm ▸ .guarded s.gate (ExplicitRuntime.Reverse.canonical s.loop).view

private theorem decode_cast {left right : List (Vertex τ Φ)} (h : left = right)
    (w : View Φ left A L B K E D) : (h ▸ w : View Φ right A L B K E D).decode = w.decode := by
  cases h
  rfl

private theorem view_decode (s : Guarded Φ A L B K E D) : (view s).decode = s := by
  calc
    _ = (View.guarded s.gate (ExplicitRuntime.Reverse.canonical s.loop).view).decode :=
      decode_cast (read_graph s).symm _
    _ = s := by
      change Guarded.mk s.gate (ExplicitRuntime.Reverse.canonical s.loop).view.decode = s
      rw [ExplicitRuntime.Reverse.canonical_decode]

noncomputable def canonical (s : Guarded Φ A L B K E D) : Decomposition (graph s) B K :=
  ⟨graphChecked s, view s, congrArg graph (view_decode s)⟩

theorem raise_canonical (s : Guarded Φ A L B K E D) : (raise (canonical s)).1 = region s :=
  congrArg region (view_decode s)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Proofs
