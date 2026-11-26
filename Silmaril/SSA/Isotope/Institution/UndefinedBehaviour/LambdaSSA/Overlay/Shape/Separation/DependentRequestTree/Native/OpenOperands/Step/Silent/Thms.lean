module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Normalize
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Cycle
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Decision

/-! # Native adequacy of bounded silent normalization -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload StatePrimitives model)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T : List Syntax.Ty} {A : Syntax.Ty} {σ : Type v}

/-- Resolving the silent prefixes preserves complete observations at each
typed feedback invocation, including productive infinite replay. -/
theorem Table.close_normalized (g : Table S R) (ok : g.normalizes = true)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) =
      Feedback.close ((g.normalized ok).feedback caller prim) (blockPoint p s) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.close_normalized
    g ok caller prim p s

/-- An exhausted silent scan yields an infinite path of native steps at
the unchanged store. Exhaustive packets give an actual repeated typed configuration. -/
theorem Table.exhausted_replay (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (configs : ConfigurationEnumeration R) (p : Packet R) (s : σ)
    (exhausted : g.resolve R.length p.1 = none) :
    ∃ path : Nat → Packet R, path 0 = p ∧
      (∀ n, Feedback.Step (g.feedback caller prim) (blockPoint (path n) s) (blockPoint (path (n + 1)) s)) ∧
      ∃ i j : Nat, i < j ∧ path i = path j :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.exhausted_replay
    g caller prim configs p s exhausted

/-- At any typed invocation, an exhausted scan has exactly ordinary
divergence in the original feedback evaluator. -/
theorem Table.exhausts_close (g : Table S R) (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ)
    (p : Packet R) (s : σ) (exhausted : g.resolve R.length p.1 = none) :
    Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.exhausts_close
    g caller prim p s exhausted

variable [DecidableEq Φ]

/-- A checked head is reached through genuine native transfers at the
typed invocation. An exhausted head instead has ordinary divergence. -/
theorem Table.head_correct (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (caller : Payload (R.get g.entry)) (p : Packet R) (prim : StatePrimitives Φ σ) (s : σ)
    {result : HeadResult S R} (found : g.head? raw caller p = some result) :
    raw = g.native ∧
      match result with
      | .ready head =>
        ∃ q, Feedback.Reaches (g.feedback caller prim) (blockPoint p s) q ∧
          g.feedback caller prim q = (head.execute prim s).routed ∧
          Feedback.close (g.feedback caller prim) (blockPoint p s) = Feedback.close (g.feedback caller prim) q
      | .diverge =>
        Feedback.close (g.feedback caller prim) (blockPoint p s) = WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.head_correct
    g raw caller p prim s found

/-- Exact native readback transports the whole decorated observation
from the original packed CFG to the normalized guarded emitter. -/
theorem Table.normalized_observes (g : Table S R) (ok : g.normalizes = true)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (s : σ) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      Shape.denote (withExitUB (g.normalized ok).native g.selected) (model prim (g.visible.bindings caller)) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.normalized_observes
    g ok raw checked caller prim s

/-- Selected exit continuations do not alter the ordinary divergence
of an exhausted entry scan. -/
theorem Table.exhausts_observes (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) (checked : g.checkNative raw = true)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (s : σ)
    (exhausted : g.resolve R.length g.entry = none) :
    Shape.denote (withExitUB raw g.selected) (model prim (g.visible.bindings caller)) s =
      WithTop.some {Outcome.diverge} :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.exhausts_observes
    g raw checked caller prim s exhausted

variable {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

/-- The comparison keeps unsupported readback and exhausted silent scans
unknown. The guarded product has no silent-divergence head. -/
theorem Table.checkEntries_none_iff :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false ∨
        g.normalizes = false ∨ h.normalizes = false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.none_iff

/-- The existing reachable-product cutoff for the normalized heads decides
deterministic refinement of the original packed endpoints. -/
theorem Table.checkEntries_accepts_iff
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (ng : g.normalizes = true) (nh : h.normalizes = true) :
    g.checkEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.accepts_iff
    hg hh ng nh

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
