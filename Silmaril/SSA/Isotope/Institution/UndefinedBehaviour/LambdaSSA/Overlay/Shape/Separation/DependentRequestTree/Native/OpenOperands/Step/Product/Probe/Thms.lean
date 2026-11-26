module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Probe

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open Syntax (Payload Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}

/-- A failed local head match has a separating terminal test at one available store. -/
theorem local_mismatch_refutes [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry)) (p : Packet R) (q : Packet T)
    (fuel : Nat) (mismatch : ¬ (g.head a p).Matches (fun _ _ => True) (h.head b q)) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.local_mismatch_refutes g h a b p q fuel mismatch

/-- A fresh store issues the shared reply and enters the embedded suffix interpreter. -/
theorem prepend_refutation [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (a : Payload (R.get g.entry)) (b : Payload (T.get h.entry))
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (p : Packet R) (q : Packet T) {f : Φ} {arg : Payload (instrSrc f)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {route : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet T}
    (lower : g.head a p = .request f arg next) (upper : h.head b q = .request f arg route)
    (answer : Packet (S.replies f))
    {fuel : Nat} (other : Primitives Φ fuel) (t : Fin fuel)
    (bad : ¬ g.observeAt a other (next answer.1 answer.2) t ≤ h.observeAt b other (route answer.1 answer.2) t) :
    ∃ prim : Primitives Φ (fuel + 1), ¬ g.observeAt a prim p 0 ≤ h.observeAt b prim q 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.prepend_refutation
    g h a b left right p q lower upper answer other t bad

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
