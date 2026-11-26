module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Probe.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives StatePrimitives)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {g : Table S R} {h : Table S T} {a : Payload (R.get g.entry)} {b : Payload (T.get h.entry)}
  {replies : ReplyEnumeration S} {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}

include left right in
theorem path_refutes {start point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) start trail point)
    (bad : g.productLocal h a b replies point = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ g.observeAt a prim start.1 0 ≤ h.observeAt b prim start.2 0 := by
  induction trail generalizing start with
  | nil =>
    have same := walk.nil_end
    subst point
    apply local_mismatch_refutes g h a b start.1 start.2 0
    intro agrees
    have good := (Head.checkPair_iff replies (fun _ _ => true) (g.head a start.1) (h.head b start.2)).mpr
      (by simpa using agrees)
    change g.productLocal h a b replies start = true at good
    rw [bad] at good
    cases good
  | cons edge trail ih =>
    obtain ⟨listed, rest⟩ := walk.uncons
    obtain ⟨f, arg, next, next', reply, lower, upper, edgeEq⟩ := Table.product_edge_forms replies listed
    obtain ⟨suffix, separates⟩ := ih rest
    rw [edgeEq] at separates
    exact prepend_refutation g h a b left right start.1 start.2 lower upper reply suffix 0 separates

include left right in
theorem native_path_refutes (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (bad : g.productLocal h a b replies point = false) :
    ∃ prim : Primitives Φ (trail.length + 1),
      ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) 0 ≤
        Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) 0 := by
  obtain ⟨prim, separates⟩ := path_refutes (left := left) (right := right) walk bad
  exact ⟨prim, by rwa [g.observe_entry raw hg, h.observe_entry raw' hh]⟩

theorem refutation_has_mismatch {σ : Type v} (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true)
    (prim : StatePrimitives Φ σ) (s : σ)
    (failed : ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
      Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s) :
    ∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail := by
  have correct := g.searchProduct_correct h a b replies left right
  cases found : g.searchProduct h a b replies left right with
  | mismatch point trail => exact ⟨point, trail, rfl⟩
  | accepted pairs =>
    rw [found] at correct
    exact (failed (g.checkProduct_sound h raw raw' hg hh a b replies pairs correct.1 prim s)).elim

theorem mismatch_iff (hg : g.checkNative raw = true) (hh : h.checkNative raw' = true) :
    (∃ point trail, g.searchProduct h a b replies left right = .mismatch point trail) ↔
      ∃ (n : Nat) (prim : Primitives Φ n) (s : Fin n),
        ¬ Shape.denote (withExitUB raw g.selected) (Syntax.model prim (g.bindings a)) s ≤
          Shape.denote (withExitUB raw' h.selected) (Syntax.model prim (h.bindings b)) s := by
  constructor
  · rintro ⟨point, trail, found⟩
    have sound := g.searchProduct_correct h a b replies left right
    rw [found] at sound
    obtain ⟨prim, bad⟩ := native_path_refutes (left := left) (right := right) hg hh sound.1 sound.2
    exact ⟨trail.length + 1, prim, 0, bad⟩
  · rintro ⟨_, prim, s, bad⟩
    exact refutation_has_mismatch hg hh prim s bad

theorem simple_length {point : ProductConfig R T} {trail : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h a b replies) (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail point)
    (simple : (ProductPath.vertices (⟨g.entry, a⟩, ⟨h.entry, b⟩) trail).Nodup) :
    trail.length + 1 ≤ (g.productVisits h a b replies left right).length := by
  let seen := (g.productVisits h a b replies left right).map Prod.fst
  have exactVisits := (g.productVisits_exact h a b replies left right).2
  have entry : (⟨g.entry, a⟩, ⟨h.entry, b⟩) ∈ seen := (exactVisits _).mpr ⟨[], .start⟩
  have closed (p : ProductConfig R T) (mem : p ∈ seen) (e : ProductEdge S R T)
      (edge : e ∈ g.productEdges h a b replies p) : e.2 ∈ seen := by
    obtain ⟨_, path⟩ := (exactVisits p).mp mem
    exact (exactVisits _).mpr ⟨_, .step path edge⟩
  have bound := simple.length_le_of_subset (walk.covered seen entry closed).2
  simpa [seen, ProductPath.vertices, Nat.succ_eq_add_one] using bound

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FiniteSupport.Model.Reachable
