module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RankedReplyRecognition

/-! # Standard Paper certificates for ranked reply-table recognition -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {Φ : Type} [Profile Φ] [DecidableEq Φ] {n : Nat}

/-- Recognition certifies literal block inlining in standard Paper. -/
theorem eqv (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} (accepted : recognize R rank s t r = some p) :
    Paper.Eqv [s.ty] r p.region [t.ty] :=
  RankedReplyRecognition.sound R rank accepted

/-- The computed control represents the original exactly typed singleton arrow. -/
theorem ofRegion_eq_native (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} (hr : ValueBranches [s.ty] r [t.ty])
    (accepted : recognize R rank s t r = some p) : Paper.TypeCategory.ofRegion hr = p.native :=
  ((Paper.TypeCategory.ofRegion_eq_iff hr p.region_typed).2 (eqv R rank accepted)).trans
    p.native_eq_ofRegion.symm

/-- The finite-reply renderer gives the native arrow at each point of the exact input shape. -/
theorem ofRegion_eq_render (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} (hr : ValueBranches [s.ty] r [t.ty])
    (accepted : recognize R rank s t r = some p) (x : s.Value) :
    point s x ≫ Paper.TypeCategory.ofRegion hr = (p.readback x).render (point t) := by
  rw [ofRegion_eq_native R rank hr accepted, p.native_eq_ofRegion, p.ofRegion_eq_readback, point_dispatch]

/-- Run the checker on an existing typed row and return the computed control and its certificate.
The packet profile supplies the exact local binder types absent from the erased table. -/
def recognizeTyped (R : Fin n → ReplyShape) (rank : Fin n → Nat) (s t : ReplyShape)
    {r : Region Φ} (hr : ValueBranches [s.ty] r [t.ty]) :
    Option {p : Control Φ s t // Paper.TypeCategory.ofRegion hr = p.native} :=
  match found : recognize R rank s t r with
  | none => none
  | some p => some ⟨p, ofRegion_eq_native R rank hr found⟩

namespace Example

theorem accepted_typed : ValueBranches [Reply.ty] accepted [Reply.ty] :=
  RankedReplyRecognition.accepted_typed

theorem backEdge_typed : ValueBranches [Reply.ty] backEdge [Reply.ty] :=
  RankedReplyRecognition.backEdge_typed

theorem captured_typed : ValueBranches [Reply.ty] captured [Reply.ty] :=
  RankedReplyRecognition.captured_typed

theorem accepts : recognize packets rank Reply Reply accepted = some expected := rfl

theorem rejects_backEdge : recognize packets rank Reply Reply backEdge = none := rfl

theorem rejects_capture : recognize packets rank Reply Reply captured = none := rfl

theorem reads_on_both_entries (x : Reply.Value) :
    point Reply x ≫ Paper.TypeCategory.ofRegion accepted_typed =
      (Row.call Recognition.Example.Op.read Row.leaf).render (point Reply) := by
  rw [ofRegion_eq_render packets rank accepted_typed accepts]
  cases x <;> rfl

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked
