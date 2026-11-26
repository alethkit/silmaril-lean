module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet)
open ProductSearch (Visit discover scan)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {edges : ProductConfig R T → List (ProductEdge S R T)}

private theorem keep_iff (removed pair : ProductConfig R T) :
    (!productContains [removed] pair.1 pair.2) = true ↔ pair ≠ removed := by
  simp [← Bool.not_eq_true, productContains_iff]

private theorem discover_some {remaining : List (ProductConfig R T)} {seen : List (Visit S R T)}
    {visit : Visit S R T} (found : discover edges remaining seen = some visit) :
    ∃ origin ∈ seen, ∃ edge ∈ edges origin.1, edge.2 ∈ remaining ∧
      visit = (edge.2, origin.2 ++ [edge]) := by
  unfold discover at found
  obtain ⟨⟨p, path⟩, member, hit⟩ := List.exists_of_findSome?_eq_some found
  obtain ⟨edge, listed, picked⟩ := List.exists_of_findSome?_eq_some hit
  split at picked
  · exact ⟨(p, path), member, edge, listed, (productContains_iff _ _ _).mp ‹_ = true›,
      (Option.some.inj picked).symm⟩
  · cases picked

private theorem discover_none {remaining : List (ProductConfig R T)} {seen : List (Visit S R T)}
    (found : discover edges remaining seen = none)
    (origin : Visit S R T) (member : origin ∈ seen) (edge : ProductEdge S R T) (listed : edge ∈ edges origin.1) :
    edge.2 ∉ remaining := by
  unfold discover at found
  have none := List.findSome?_eq_none_iff.mp (List.findSome?_eq_none_iff.mp found origin member) edge listed
  intro mem
  simp [show productContains remaining edge.2.1 edge.2.2 = true from (productContains_iff _ _ _).mpr mem] at none

/-- The inventory bounds the number of discoveries. Every recorded path
is valid and the final inventory of visited configurations is closed. -/
theorem scan_spec (start : ProductConfig R T) (fuel : Nat)
    (remaining : List (ProductConfig R T)) (seen : List (Visit S R T))
    (bound : remaining.length ≤ fuel)
    (cover : ∀ p, p ∈ remaining ∨ p ∈ seen.map Prod.fst)
    (paths : ∀ v ∈ seen, ProductPath edges start v.2 v.1) :
    let out := scan edges fuel remaining seen
    (∀ v ∈ seen, v ∈ out) ∧
      (∀ v ∈ out, ProductPath edges start v.2 v.1) ∧
      ∀ v ∈ out, ∀ edge ∈ edges v.1, edge.2 ∈ out.map Prod.fst := by
  induction fuel generalizing remaining seen with
  | zero =>
    have empty : remaining = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero bound)
    exact ⟨fun _ h => h, paths, fun v hv edge he => (cover edge.2).resolve_left (by simp [empty])⟩
  | succ fuel ih =>
    rw [scan]
    cases found : discover edges remaining seen with
    | none =>
      exact ⟨fun _ h => h, paths, fun v hv edge he =>
        (cover edge.2).resolve_left (discover_none found v hv edge he)⟩
    | some visit =>
      obtain ⟨parent, listed, edge, member, active, rfl⟩ := discover_some found
      let visit : Visit S R T := (edge.2, parent.2 ++ [edge])
      let rest := remaining.filter fun p => !productContains [visit.1] p.1 p.2
      have shrinks : rest.length < remaining.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨edge.2, active, fun kept => (keep_iff visit.1 edge.2).mp kept rfl⟩
      have cover' (p) : p ∈ rest ∨ p ∈ (visit :: seen).map Prod.fst := by
        obtain left | right := cover p
        · by_cases same : p = visit.1
          · exact .inr (by simp [same])
          · exact .inl (List.mem_filter.mpr ⟨left, (keep_iff _ _).mpr same⟩)
        · exact .inr (List.mem_cons_of_mem _ right)
      have paths' (v) (hv : v ∈ visit :: seen) : ProductPath edges start v.2 v.1 := by
        rcases List.mem_cons.mp hv with rfl | prior
        · exact .step (paths parent listed) member
        · exact paths v prior
      obtain ⟨retained, valid, closed⟩ := ih rest (visit :: seen) (Nat.lt_succ_iff.mp (shrinks.trans_le bound)) cover' paths'
      exact ⟨fun v hv => retained v (List.mem_cons_of_mem _ hv), valid, closed⟩

theorem check_pair_edges [DecidableEq Φ] (replies : ReplyEnumeration S)
    (rel : Packet R → Packet T → Bool) (p : Head S R) (q : Head S T) :
    p.checkPair replies rel q =
      (p.checkPair replies (fun _ _ => true) q &&
        (p.productEdges replies q).all fun edge => rel edge.2.1 edge.2.2) := by
  cases p with
  | exit i marked =>
    cases q with
    | exit j marked' => cases marked <;> cases marked' <;> simp [Head.checkPair, Head.productEdges]
    | request => cases marked <;> rfl
  | request f arg next =>
    cases q with
    | exit i marked => cases marked <;> rfl
    | request g arg' next' =>
      simp only [Head.checkPair, Head.productEdges]
      split
      · simp [*, List.all_map, Function.comp_def]
      · simp [*]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
