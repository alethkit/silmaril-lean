module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Soundness

/-! # Soundness of closed finite relations for native guarded feedback -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {σ : Type v}

theorem Head.checkPair_iff [DecidableEq Φ] (replies : ReplyEnumeration S)
    (related : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies related q = true ↔ p.Matches (fun x y => related x y = true) q :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.check_pair_iff
    replies related p q

theorem productContains_iff (pairs : List (Packet R × Packet T)) (p : Packet R) (q : Packet T) :
    productContains pairs p q = true ↔ (p, q) ∈ pairs :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_contains_iff
    pairs p q

/-- A closed relation gives refinement at every related pair and common
initial state. The infinite case uses native feedback's ordinary divergence. -/
theorem Table.closed_relation_sound (g : Table S R) (h : Table S T)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (prim : Syntax.StatePrimitives Φ σ) (rel : Packet R → Packet T → Prop)
    (closed : ∀ p q, rel p q → (g.head caller p).Matches rel (h.head caller' q))
    {p : Packet R} {q : Packet T} (related : rel p q) (s : σ) :
    g.observeAt caller prim p s ≤ h.observeAt caller' prim q s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.closed_relation_sound
    g h caller caller' prim rel closed related s

/-- Acceptance, together with exact native readback, proves refinement of
the original decorated runners for each deterministic shaped interpreter. -/
theorem Table.checkProduct_sound [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (pairs : List (Packet R × Packet T))
    (checked : g.checkProduct h caller caller' replies pairs = true)
    (prim : Syntax.StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings caller)) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings caller')) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.product_sound
    g h raw raw' readback readback' caller caller' replies pairs checked prim s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
