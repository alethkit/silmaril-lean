module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Separation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Decision

/-! # Finite-store completeness for the exact guarded product -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives StatePrimitives)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ}
  {A : Syntax.Ty} {R T : List Syntax.Ty} {g : Table S R} {h : Table S T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}
  {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}

/-- The actual guarded product cannot accept a refuting pair of runs, even
when one of the runs has infinite replay on an arbitrary store. -/
theorem Table.refutation_has_product_mismatch {σ : Type v}
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s) :
    ∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.refutation_has_mismatch
    hg hh prim s failed

include left right in
/-- A path to a local mismatch can be replayed by one total interpreter.
There is one fresh store per shared reply and one for the terminal test. -/
theorem Table.product_path_refutes (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (bad : g.productLocal h a b replies point = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) 0 ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) 0 :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.native_path_refutes
    (left := left) (right := right) hg hh walk bad

/-- Product rejection characterizes the existence of a refuting finite
deterministic interpreter. Any arbitrary-store refutation also forces rejection. -/
theorem Table.product_mismatch_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    (∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail) ↔
      ∃ (n : Nat) (prim : Primitives Φ n) (s : Fin n),
        ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.mismatch_iff
    hg hh

/-- The computed reachable-pair count bounds the size of every simple
shared reply path, including its final test pair. -/
theorem Table.simple_product_path_bound
    {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (simple : (ProductPath.vertices (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail).Nodup) :
    trail.length + 1 ≤ (g.productVisits h a b replies left right).length :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.simple_length
    walk simple

variable {callers : CallerEnumeration A}
  {decodeLeft : Payload A → Payload (R.get g.entry)} {decodeRight : Payload A → Payload (T.get h.entry)}

/-- Unsupported readback remains unknown, regardless of rank or cutoff. -/
theorem Table.checkReachableEntries_none_iff :
    g.checkReachableEntries? h raw raw' callers decodeLeft decodeRight replies left right = none ↔
      g.checkNative raw = false ∨ h.checkNative raw' = false :=
  Table.checkEntries_none_iff

/-- An arbitrary-store refutation gives a negative verdict at the
computed cutoff, at the original caller. -/
theorem Table.checkReachableEntries_rejects_of_refutation {σ : Type v}
    (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (callers : CallerEnumeration A) (replies : ReplyEnumeration S)
    (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T)
    (input : Payload A) (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings (decodeLeft input))) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings (decodeRight input))) s) :
    g.checkReachableEntries? h raw raw' callers decodeLeft decodeRight replies left right = some false :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.rejects
    hg hh callers replies left right input prim s failed

/-- The finite comparison at the reachable-product cutoff is exact over
arbitrary deterministic stores. Neither endpoint needs an entry rank. -/
theorem Table.checkReachableEntries_accepts_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    g.checkReachableEntries? h raw raw' callers decodeLeft decodeRight replies left right = some true ↔
      g.DeterministicRefines.{u,v} h raw raw' decodeLeft decodeRight :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable.accepts_iff
    hg hh

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
