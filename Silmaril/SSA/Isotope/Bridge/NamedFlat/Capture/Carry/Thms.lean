module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Typed
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Tree

public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry

open LambdaSSA (FiniteCFG)
open LambdaSSA.Semantics (Env)
open LambdaSSA.Semantics.Interaction (Primitive region)

universe u v w x
variable {F : Type v} {blocks exits n : Nat}

theorem graph_hasType {τ : Type u} [TypeFormers τ] [HasTy F τ]
    {β : BoundCtx τ n} {R : Fin blocks → τ} {D : Fin exits → τ}
    {g : FiniteCFG F blocks exits n} (typed : g.HasType β R D) (slot : Fin n) :
    (graph g slot).HasType β (packetTypes R β slot) D :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graph_hasType typed slot

/-- Adding and decoding the caller field preserves the weak ITree at every
caller environment, including the original order and values of outward exits.
The internal simulation uses the existing iterator's uniformity law. -/
theorem graph_tree {Events : Type w → Type w} {α : Type x}
    (raw : Primitive Events F α) (g : FiniteCFG F blocks exits n) (slot : Fin n) (env : Env α) :
    region raw env (graph g slot).erase = region raw env g.erase :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.graph_tree raw g slot env

end Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
