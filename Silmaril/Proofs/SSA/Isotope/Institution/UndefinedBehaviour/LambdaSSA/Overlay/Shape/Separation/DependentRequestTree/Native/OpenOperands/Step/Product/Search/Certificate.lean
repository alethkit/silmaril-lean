module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Traversal

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open ProductSearch (Visit)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}

variable (g : Table S R) (h : Table S T)
  (caller : Syntax.Payload (R.get g.entry)) (caller' : Syntax.Payload (T.get h.entry))
  (replies : ReplyEnumeration S)

theorem visits_spec (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
    let edges := g.productEdges h caller caller' replies
    let seen := g.productVisits h caller caller' replies left right
    (entry, []) ∈ seen ∧
      (∀ v ∈ seen, ProductPath edges entry v.2 v.1) ∧
      (∀ v ∈ seen, ∀ edge ∈ edges v.1, edge.2 ∈ seen.map Prod.fst) ∧
      (seen.map Prod.fst).Nodup := by
  let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
  let edges := g.productEdges h caller caller' replies
  let remaining := (left.configs.product right.configs).filter fun p => !productContains [entry] p.1 p.2
  let seeds : List (Visit S R T) := [(entry, [])]
  have cover (p : ProductConfig R T) : p ∈ remaining ∨ p ∈ seeds.map Prod.fst := by
    by_cases same : p = entry
    · exact .inr (by simp [same, seeds])
    · have absent : productContains [entry] p.1 p.2 = false := Bool.eq_false_iff.mpr fun hit =>
        same (List.mem_singleton.mp ((productContains_iff _ _ _).mp hit))
      exact .inl (List.mem_filter.mpr ⟨List.mem_product.mpr ⟨left.complete p.1, right.complete p.2⟩, by simp [absent]⟩)
  have initial (v : Visit S R T) (listed : v ∈ seeds) : ProductPath edges entry v.2 v.1 := by
    obtain rfl := List.mem_singleton.mp listed
    exact .start
  have disjoint (p : ProductConfig R T) (listed : p ∈ remaining) : p ∉ seeds.map Prod.fst := by
    intro found
    have same : p = entry := by simpa [seeds] using found
    subst p
    have kept := (List.mem_filter.mp listed).2
    simp [productContains] at kept
  obtain ⟨retains, paths, closed, unique⟩ :=
    scan_spec entry remaining.length remaining seeds (Nat.le_refl _) cover initial (by simp [seeds]) disjoint
  exact ⟨retains _ (List.mem_singleton_self _), paths, closed, unique⟩

theorem visits_exact (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
    let edges := g.productEdges h caller caller' replies
    let seen := g.productVisits h caller caller' replies left right
    (seen.map Prod.fst).Nodup ∧
      ∀ p, p ∈ seen.map Prod.fst ↔ ∃ trail, ProductPath edges entry trail p := by
  let seen := g.productVisits h caller caller' replies left right
  obtain ⟨entry, paths, closed, unique⟩ := visits_spec g h caller caller' replies left right
  have start : (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) ∈ seen.map Prod.fst :=
    List.mem_map.mpr ⟨_, entry, rfl⟩
  have successor (p : ProductConfig R T) (listed : p ∈ seen.map Prod.fst)
      (edge : ProductEdge S R T) (he : edge ∈ g.productEdges h caller caller' replies p) :
      edge.2 ∈ seen.map Prod.fst := by
    obtain ⟨visit, member, rfl⟩ := List.mem_map.mp listed
    exact closed visit member edge he
  exact ⟨unique, fun p => ⟨fun listed => by
    obtain ⟨visit, member, rfl⟩ := List.mem_map.mp listed
    exact ⟨visit.2, paths visit member⟩,
    fun ⟨_, walk⟩ => (path_covered walk _ start successor).1⟩⟩

theorem search_correct (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    match g.searchProduct h caller caller' replies left right with
    | .accepted pairs => g.checkProduct h caller caller' replies pairs = true ∧
      ∀ pair ∈ pairs, ∃ path, ProductPath (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair
    | .mismatch pair path =>
      ProductPath (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩) path pair ∧
      g.productLocal h caller caller' replies pair = false := by
  let entry : ProductConfig R T := (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
  let edges := g.productEdges h caller caller' replies
  let seen := g.productVisits h caller caller' replies left right
  obtain ⟨initial, paths, closed, _⟩ := visits_spec g h caller caller' replies left right
  let bad := fun v : Visit S R T => !g.productLocal h caller caller' replies v.1
  change (match (match seen.find? bad with
    | none => ProductSearch.Result.accepted (seen.map Prod.fst)
    | some (pair, path) => ProductSearch.Result.mismatch pair path) with
    | .accepted pairs => g.checkProduct h caller caller' replies pairs = true ∧
      ∀ pair ∈ pairs, ∃ path, ProductPath edges entry path pair
    | .mismatch pair path => ProductPath edges entry path pair ∧ g.productLocal h caller caller' replies pair = false)
  cases found : seen.find? bad with
  | none =>
    constructor
    · rw [Table.checkProduct]
      refine Bool.and_eq_true_iff.mpr ⟨?_, List.all_eq_true.mpr ?_⟩
      · apply (productContains_iff _ _ _).mpr
        exact List.mem_map.mpr ⟨(entry, []), initial, rfl⟩
      · intro pair inPairs
        obtain ⟨⟨p, trail⟩, listed, rfl⟩ := List.mem_map.mp inPairs
        change (g.head caller p.1).checkPair replies (productContains (seen.map Prod.fst))
          (h.head caller' p.2) = true
        rw [check_pair_edges]
        refine Bool.and_eq_true_iff.mpr ⟨?_, List.all_eq_true.mpr ?_⟩
        · have good := List.find?_eq_none.mp found (p, trail) listed
          simpa [bad, Table.productLocal] using good
        · intro edge member
          exact (productContains_iff _ _ _).mpr (closed (p, trail) listed edge member)
    · intro pair listed
      obtain ⟨⟨p, trail⟩, visited, rfl⟩ := List.mem_map.mp listed
      exact ⟨trail, paths (p, trail) visited⟩
  | some visit =>
    obtain ⟨p, trail⟩ := visit
    exact ⟨paths (p, trail) (List.mem_of_find?_eq_some found), by
      simpa [bad] using List.find?_some found⟩

private theorem checked_at {pairs : List (ProductConfig R T)}
    (ok : g.checkProduct h caller caller' replies pairs = true)
    (pair : ProductConfig R T) (listed : pair ∈ pairs) :
    g.productLocal h caller caller' replies pair = true ∧
      ∀ edge ∈ g.productEdges h caller caller' replies pair, edge.2 ∈ pairs := by
  have localCheck := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).2 pair listed
  change (g.head caller pair.1).checkPair replies (productContains pairs) (h.head caller' pair.2) = true at localCheck
  rw [check_pair_edges] at localCheck
  obtain ⟨good, all⟩ := Bool.and_eq_true_iff.mp localCheck
  exact ⟨good, fun edge member => (productContains_iff _ _ _).mp (List.all_eq_true.mp all edge member)⟩

private theorem path_mem {pairs : List (ProductConfig R T)} {trail : List (ProductEdge S R T)}
    {pair : ProductConfig R T} (ok : g.checkProduct h caller caller' replies pairs = true)
    (path : ProductPath (g.productEdges h caller caller' replies) (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      trail pair) : pair ∈ pairs := by
  induction path with
  | start => exact (productContains_iff _ _ _).mp (Bool.and_eq_true_iff.mp ok).1
  | step _ member ih => exact (checked_at g h caller caller' replies ok _ ih).2 _ member

theorem search_accepts_iff (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    (∃ pairs, g.searchProduct h caller caller' replies left right = .accepted pairs) ↔
    ∃ pairs, g.checkProduct h caller caller' replies pairs = true := by
  have computed := search_correct g h caller caller' replies left right
  constructor
  · rintro ⟨pairs, found⟩
    rw [found] at computed
    exact ⟨pairs, computed.1⟩
  · rintro ⟨pairs, ok⟩
    cases found : g.searchProduct h caller caller' replies left right with
    | accepted cert => exact ⟨cert, rfl⟩
    | mismatch pair trail =>
      rw [found] at computed
      obtain ⟨path, bad⟩ := computed
      have good := (checked_at g h caller caller' replies ok pair (path_mem g h caller caller' replies ok path)).1
      rw [good] at bad
      cases bad

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
