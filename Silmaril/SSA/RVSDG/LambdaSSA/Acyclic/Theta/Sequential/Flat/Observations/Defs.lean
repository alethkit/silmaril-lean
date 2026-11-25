module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse.Defs

/-! # Recover two checked components into one flat LambdaSSA CFG -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A I B K M C J E D : τ}
variable {g : Conditional.Graph Φ A I M M} {h : ExplicitRuntime.Graph Φ M E D}

/-- The component decompositions contain numbered graph structure and its
wiring certificates. The producer's exits have the consumer's entry type. -/
def recover (first : Conditional.Reverse.Decomposition g B K)
    (second : ExplicitRuntime.Reverse.Decomposition h C J) : Fragment Φ A E D :=
  link (Fragment.guarded first.view.decode) (Fragment.loop second.view.decode)

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Sequential.Flat
