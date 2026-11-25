module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Defs
public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Reverse.Defs

/-! # Structural recovery from a numbered conditional θ graph -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse

open Isotope.LambdaSSA (Region)
open OrderedTheta (carriedData)
open NestedTheta.ExplicitRuntime (EntryChecked)
open TwoBlock.TwoExit (Carrier)
open ExplicitRuntime.Reverse (Vertex LoopView read)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A L B K E D : τ}

inductive View (Φ : Type u) [HasTy Φ τ] : List (Vertex τ Φ) → τ → τ → τ → τ → τ → τ → Type u where
  | guarded {A L B K E D : τ} {body : List (Vertex τ Φ)}
      (gate : TwoBlock.Instruction Φ A (Carrier L E D)) (loop : LoopView Φ body L B K E D) :
      View Φ [.classifier gate, .gamma [[], body]] A L B K E D

def View.decode {labels : List (Vertex τ Φ)} : View Φ labels A L B K E D → Guarded Φ A L B K E D
  | .guarded gate loop => ⟨gate, loop.decode⟩

/-- The supplied parse reads the classifier, empty bypass and existing loop
from the graph. Its wiring certificate also fixes the γ continuation. -/
structure Decomposition (g : Graph Φ A L E D) (B K : τ) where
  checked : EntryChecked (a := carriedData A) (b := carriedData (Carrier L E D)) g.toTerm
  view : View Φ (read g.toTerm) A L B K E D
  wiring : graph view.decode = g

abbrev Fibre (g : Graph Φ A L E D) (B K : τ) :=
  Σ r : Region Φ, Related A L B K E D r g

def raise {g : Graph Φ A L E D} (w : Decomposition g B K) : Fibre g B K :=
  let source := region w.view.decode
  ⟨source, Eq.mp (congrArg (Related A L B K E D source) w.wiring) (.guarded w.view.decode)⟩

theorem fibre_inhabited {g : Graph Φ A L E D} (w : Decomposition g B K) :
    Nonempty (Fibre g B K) :=
  ⟨raise w⟩

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional.Reverse
