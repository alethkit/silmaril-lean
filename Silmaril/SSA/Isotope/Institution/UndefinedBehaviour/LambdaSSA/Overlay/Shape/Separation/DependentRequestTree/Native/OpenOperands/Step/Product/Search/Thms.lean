module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Certificate

/-! # Reachability and certificate exactness of guarded product search -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
variable (g : Table S R) (h : Table S T)
  (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
  (replies : ReplyEnumeration S)

/-- A successful search returns a closed certificate of reachable pairs.
A mismatch has a typed shared reply path and fails the local comparison. -/
theorem Table.searchProduct_correct (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    match g.searchProduct h caller caller' replies left right with
    | .accepted pairs => g.checkProduct h caller caller' replies pairs = true ∧
      ∀ pair ∈ pairs, ∃ path, ProductPath (g.productEdges h caller caller' replies)
        (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair
    | .mismatch pair path =>
      ProductPath (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair ∧
      g.productLocal h caller caller' replies pair = false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.search_correct
    g h caller caller' replies left right

/-- Search succeeds exactly when a closed certificate containing the entry
is accepted by the existing checker. -/
theorem Table.searchProduct_accepts_iff (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    (∃ pairs, g.searchProduct h caller caller' replies left right = .accepted pairs) ↔
    ∃ pairs, g.checkProduct h caller caller' replies pairs = true :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.search_accepts_iff
    g h caller caller' replies left right

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
