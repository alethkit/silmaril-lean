module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Normalize
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Readback
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction hiding Row Table
open OpenOperands (CallerEnumeration ReplyEnumeration ConfigurationEnumeration)
open OpenOperands.Silent
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration hiding Row Table
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty}
  {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

theorem accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (ng : g.normalizes = true) (nh : h.normalizes = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight := by
  have guard : (g.checkNative raw && h.checkNative raw') = true := Bool.and_eq_true_iff.mpr ⟨hg, hh⟩
  rw [OpenOperands.Silent.Table.checkEntries?, ite_eq_left guard, dite_eq_left ng, dite_eq_left nh,
    OpenOperands.Table.checkReachableEntries_accepts_iff (guarded_readback_self _) (guarded_readback_self _)]
  unfold OpenOperands.Silent.Table.DeterministicRefines OpenOperands.Table.DeterministicRefines
  constructor
  · intro normalized σ input prim s
    rw [normalized_observes g ng raw hg (decodeLeft input) prim s,
      normalized_observes h nh raw' hh (decodeRight input) prim s]
    exact normalized σ input prim s
  · intro original σ input prim s
    have passed := original σ input prim s
    rw [normalized_observes g ng raw hg (decodeLeft input) prim s,
      normalized_observes h nh raw' hh (decodeRight input) prim s] at passed
    exact passed

theorem none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false ∨
        g.normalizes = false ∨ h.normalizes = false := by
  cases gl : g.checkNative raw <;> cases hr : h.checkNative raw' <;>
    cases lg : g.normalizes <;> cases rh : h.normalizes <;>
    simp [OpenOperands.Silent.Table.checkEntries?, gl, hr, lg, rh,
      OpenOperands.Table.checkReachableEntries_none_iff, guarded_readback_self]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
