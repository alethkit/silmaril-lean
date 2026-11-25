module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Expansion.Defs
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

public section

universe u v w z

namespace Silmaril.Calco2019.Proofs.IterationExpansion

open IterationTheory

variable {σ : Signature.{u}} {E : Type v} {S : Type w} {T : Type z}

theorem exists_route (p : S → T) (a b : Head σ E S)
    (same : a.mapState p = b.mapState p) (distinct : a.HasDistinctArguments) :
    ∃ route : S → S, (∀ s, p (route s) = p s) ∧ a.mapState route = b := by
  classical
  cases a <;> cases b <;> simp [Head.mapState, Head.HasDistinctArguments] at same distinct
  · exact ⟨id, fun _ => rfl, rfl⟩
  · rename_i e e'
    subst e'
    exact ⟨id, fun _ => rfl, rfl⟩
  · rename_i sym l sym' r
    obtain ⟨eq, heq⟩ := same
    subst sym'
    have args : p ∘ l = p ∘ r := eq_of_heq heq
    let route (s : S) := if h : ∃ i, l i = s then r (Classical.choose h) else s
    have fiber (s : S) : p (route s) = p s := by
      by_cases hs : ∃ i, l i = s
      · rw [show route s = r (Classical.choose hs) from dite_eq_left hs]
        exact (congrFun args (Classical.choose hs)).symm.trans
          (congrArg p (Classical.choose_spec hs))
      · rw [show route s = s from dite_eq_right hs]
    have at_arg (i : Fin (σ.arity sym)) : route (l i) = r i := by
      let hi := show ∃ j, l j = l i from ⟨i, rfl⟩
      exact (dite_eq_left hi).trans (congrArg r (distinct (Classical.choose_spec hi)))
    exact ⟨route, fiber, congrArg (Head.node sym) (funext at_arg)⟩

variable (g : System σ E S) (pick : T → S) (p : S → T)

private theorem distinct_withArguments {R : Type*} (e : Head σ E S) (f : Fin e.slots → R)
    (hf : Function.Injective f) : (e.withArguments f).HasDistinctArguments := by
  cases e
  · trivial
  · trivial
  · exact hf

theorem distinct_representative (t : T) : (representativeBody g pick t).HasDistinctArguments := by
  apply distinct_withArguments
  intro i j h
  exact eq_of_heq (Sigma.mk.inj_iff.1 (Sum.inr.inj h)).2

private theorem map_withArguments {R Q : Type*} (e : Head σ E S) (f : Fin e.slots → R)
    (p : R → Q) :
    (e.withArguments f).mapState p = e.withArguments (p ∘ f) := by
  cases e <;> rfl

private theorem arguments_map {Q : Type*} (e : Head σ E S) (p : S → Q) :
    e.withArguments (p ∘ e.argument) = e.mapState p := by
  cases e <;> rfl

private theorem map_comp {R : Type*} (e : Head σ E S) (a : S → T) (b : T → R) :
    (e.mapState a).mapState b = e.mapState (b ∘ a) := by
  cases e <;> rfl

theorem expanded_respects {h : System σ E T} (map : PreservesEquations g h p) :
    PreservesEquations (expandedSystem g pick) h (expandedProjection g pick p) := by
  intro x
  unfold expandedSystem
  rw [map_comp]
  exact map (originalState g pick x)

theorem representative_respects {h : System σ E T} (map : PreservesEquations g h p)
    (section_eq : ∀ t, p (pick t) = t) (t : T) :
    (representativeBody g pick t).mapState (expandedProjection g pick p) = h t := by
  have hbase := map (pick t)
  rw [section_eq] at hbase
  refine Eq.trans ?_ hbase
  unfold representativeBody
  rw [map_withArguments]
  exact arguments_map (g (pick t)) p

theorem expansion_routes {h : System σ E T} (map : PreservesEquations g h p)
    (section_eq : ∀ t, p (pick t) = t) :
    ∃ route : ExpandedState g pick → ExpandedState g pick → ExpandedState g pick,
      (∀ x y, expandedProjection g pick p (route x y) = expandedProjection g pick p y) ∧
      (∀ x, (representativeBody g pick (expandedProjection g pick p x)).mapState (route x) =
        expandedSystem g pick x) := by
  classical
  have hroute (x : ExpandedState g pick) := exists_route (expandedProjection g pick p)
    (representativeBody g pick (expandedProjection g pick p x)) (expandedSystem g pick x)
    ((representative_respects g pick p map section_eq _).trans ((expanded_respects g pick p map x).symm))
    (distinct_representative g pick _)
  exact ⟨fun x => Classical.choose (hroute x),
    fun x => (Classical.choose_spec (hroute x)).1,
    fun x => (Classical.choose_spec (hroute x)).2⟩

theorem expansion_finite [Finite S] [Finite T] : Finite (ExpandedState g pick) := by
  let : Fintype S := Fintype.ofFinite S
  let : Fintype T := Fintype.ofFinite T
  infer_instance

end Silmaril.Calco2019.Proofs.IterationExpansion
