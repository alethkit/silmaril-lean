module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Certificate

import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Traversal

/-! # Reachability and certificate exactness of guarded product search -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open Syntax (Payload)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
section Paths

variable {edges : ProductConfig R T → List (ProductEdge S R T)}
  {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}

theorem ProductPath.nil_end (walk : ProductPath edges start [] point) : start = point :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_nil walk

theorem ProductPath.uncons {edge : ProductEdge S R T}
    (walk : ProductPath edges start (edge :: trail) point) :
    edge ∈ edges start ∧ ProductPath edges edge.2 trail point :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_uncons walk

/-- A shortest path to a fixed pair cannot revisit a pair. -/
theorem ProductPath.shortest (walk : ProductPath edges start trail point) :
    ∃ shortest, ProductPath edges start shortest point ∧
      (ProductPath.vertices start shortest).Nodup ∧
      ∀ other, ProductPath edges start other point → shortest.length ≤ other.length :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_shortest walk

theorem ProductPath.covered (walk : ProductPath edges start trail point) (domain : List (ProductConfig R T))
    (initial : start ∈ domain)
    (closed : ∀ p ∈ domain, ∀ edge ∈ edges p, edge.2 ∈ domain) :
    point ∈ domain ∧ ProductPath.vertices start trail ⊆ domain :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.path_covered walk domain initial closed

variable [DecidableEq Φ]

theorem Table.product_edge_forms {g : Table S R} {h : Table S T}
    {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)} (replies : ReplyEnumeration S)
    {p : ProductConfig R T} {edge : ProductEdge S R T}
    (listed : edge ∈ g.productEdges h caller caller' replies p) :
    ∃ (f : Φ) (arg : Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R)
      (next' : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T)
      (reply : Packet (S.replies f)),
      g.head caller p.1 = .request f arg next ∧ h.head caller' p.2 = .request f arg next' ∧
      edge = (⟨f, reply⟩, next reply.1 reply.2, next' reply.1 reply.2) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.edge_forms replies listed

end Paths

variable [DecidableEq Φ]

variable (g : Table S R) (h : Table S T)
  (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
  (replies : ReplyEnumeration S)

/-- The computed visits count exactly the distinct reachable typed pairs. -/
theorem Table.productVisits_exact (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
    let edges := g.productEdges h caller caller' replies
    let seen := g.productVisits h caller caller' replies left right
    (seen.map Prod.fst).Nodup ∧
      ∀ p, p ∈ seen.map Prod.fst ↔ ∃ trail, ProductPath edges entry trail p :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.visits_exact
    g h caller caller' replies left right

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
