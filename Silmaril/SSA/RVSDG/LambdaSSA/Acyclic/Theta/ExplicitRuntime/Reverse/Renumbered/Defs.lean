module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Defs

/-! # Reverse translation with supplied typed graph isomorphisms -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered

open Isotope.LambdaSSA (Region)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K E D : τ} {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- The representative supplies the parse and the exact wire check. The
actual graph is checked by an indexed isomorphism to that representative. -/
structure Decomposition (g : Numbered Φ A E D sigs) (B K : τ) where
  representative : Graph Φ A E D
  parse : Reverse.Decomposition representative B K
  numbering : NestedTheta.Graph.Isomorphic (Op Φ) g representative

/-- A source region and an actual graph can be related through a representative
even when the graph's vertex table uses different indices. -/
structure Related (g : Numbered Φ A E D sigs) (B K : τ) (r : Region Φ) where
  representative : Graph Φ A E D
  source : ExplicitRuntime.Related A B K E D r representative
  numbering : NestedTheta.Graph.Isomorphic (Op Φ) g representative

abbrev Fibre (g : Numbered Φ A E D sigs) (B K : τ) :=
  Σ r : Region Φ, Related g B K r

def raise {g : Numbered Φ A E D sigs} (d : Decomposition g B K) : Fibre g B K :=
  let recovered := Reverse.raise d.parse
  ⟨recovered.1, ⟨d.representative, recovered.2, d.numbering⟩⟩

theorem fibre_inhabited {g : Numbered Φ A E D sigs} (d : Decomposition g B K) :
    Nonempty (Fibre g B K) :=
  ⟨raise d⟩

theorem Related.typing {g : Numbered Φ A E D sigs} {r : Region Φ} (w : Related g B K r) :
    Region.HasType [A] r [E,D] :=
  w.source.typing

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Renumbered
