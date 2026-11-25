module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Observations.Defs
import Mathlib.Data.Fintype.Prod

public section

universe u v w z

namespace Silmaril.Calco2019.Proofs.IterationObservations

open OmegaCompletePartialOrder Silmaril.Semantics.Domain IterationTheory

variable {σ : Signature.{u}} {P : Type v} {S : Type w} {T : Type z}

theorem least_paths (g : System σ P S) (s : S) (p : List Nat) :
    fix (update g) s p = observe g s p := by
  induction p generalizing s with
  | nil =>
    have h := congrFun (congrFun (fix_eq (update g)) s) []
    refine h.symm.trans ?_
    cases hs : g s <;> simp [update, observe, hs]
  | cons k p ih =>
    have h := congrFun (congrFun (fix_eq (update g)) s) (k :: p)
    refine h.symm.trans ?_
    cases hs : g s <;> simp [update, observe, hs]
    split
    · simpa [update] using ih _
    · rfl

theorem paths_of_bisim {g : System σ P S} {h : System σ P T} {R : S → T → Prop}
    (sim : Bisimulation g h R) {s : S} {t : T} (rel : R s t) (p : List Nat) :
    observe g s p = observe h t p := by
  induction p generalizing s t with
  | nil =>
    generalize gs : g s = a
    generalize ht : h t = b
    have mh : HeadMatch R a b := gs ▸ ht ▸ sim s t rel
    cases mh <;> simp [observe, gs, ht]
  | cons k p ih =>
    generalize gs : g s = a
    generalize ht : h t = b
    have mh : HeadMatch R a b := gs ▸ ht ▸ sim s t rel
    cases mh with
    | bottom => simp [observe, gs, ht]
    | exit p => simp [observe, gs, ht]
    | node a left right r =>
      by_cases b : k < σ.arity a
      · simpa [observe, gs, ht, b] using ih (r ⟨k, b⟩)
      · simp [observe, gs, ht, b]

theorem bisim_of_paths (g : System σ P S) (h : System σ P T) :
    Bisimulation g h (fun s t => observe g s = observe h t) := by
  intro s t obs
  have root := congrFun obs []
  cases gs : g s <;> cases ht : h t
  all_goals simp [observe, gs, ht, Part.some_inj, Part.none_ne_some, Part.some_ne_none,
    show (⊥ : Part (σ.Symbol ⊕ P)) = Part.none from rfl] at root
  · exact .bottom
  · rename_i p q
    subst q
    exact .exit p
  · rename_i a left b right
    subst b
    refine .node a left right ?_
    intro j
    funext path
    have eq := congrFun obs (j.val :: path)
    simpa [observe, gs, ht, j.isLt] using eq

theorem least_eq_iff_bisim (g : System σ P S) (h : System σ P T) (s : S) (t : T) :
    fix (update g) s = fix (update h) t ↔
      ∃ R : S → T → Prop, Bisimulation g h R ∧ R s t := by
  constructor
  · intro equal
    refine ⟨fun s t => observe g s = observe h t, bisim_of_paths g h, ?_⟩
    funext p
    exact (least_paths g s p).symm.trans ((congrFun equal p).trans (least_paths h t p))
  · rintro ⟨R, good, related⟩
    funext p
    exact (least_paths g s p).trans ((paths_of_bisim good related p).trans (least_paths h t p).symm)

theorem paths_of_hom {g : System σ P S} {h : System σ P T} {f : S → T}
    (hom : PreservesEquations g h f) (s : S) (p : List Nat) :
    observe g s p = observe h (f s) p := by
  have sim : Bisimulation g h (fun s t => f s = t) := by
    intro x y eq
    subst y
    rw [← hom x]
    cases gx : g x with
    | bottom => exact .bottom
    | exit q => exact .exit q
    | node a child => exact .node a child (f ∘ child) fun _ => rfl
  exact paths_of_bisim sim rfl p

theorem relation_span {g : System σ P S} {h : System σ P T} {R : S → T → Prop}
    (sim : Bisimulation g h R) :
    ∃ k : System σ P {st : S × T // R st.1 st.2},
      PreservesEquations k g (fun st => st.val.1) ∧
      PreservesEquations k h (fun st => st.val.2) := by
  classical
  let Z := {st : S × T // R st.1 st.2}
  let left : Z → S := fun st => st.val.1
  let right : Z → T := fun st => st.val.2
  have head (a : Head σ P S) (b : Head σ P T) (hm : HeadMatch R a b) :
      ∃ c : Head σ P Z, c.mapState left = a ∧ c.mapState right = b := by
    cases hm with
    | bottom => exact ⟨.bottom, rfl, rfl⟩
    | exit p => exact ⟨.exit p, rfl, rfl⟩
    | node sym l r rel =>
      exact ⟨.node sym (fun i => ⟨(l i, r i), rel i⟩), rfl, rfl⟩
  have exists_head (st : Z) :
      ∃ c : Head σ P Z, c.mapState left = g (left st) ∧ c.mapState right = h (right st) :=
    head _ _ (sim _ _ st.property)
  exact ⟨fun st => Classical.choose (exists_head st),
    fun st => (Classical.choose_spec (exists_head st)).1,
    fun st => (Classical.choose_spec (exists_head st)).2⟩

theorem least_eq_iff_finite_span [Finite S] [Finite T]
    (g : System σ P S) (h : System σ P T) (s : S) (t : T) :
    fix (update g) s = fix (update h) t ↔
      ∃ (Z : Type (max w z)) (_ : Finite Z) (k : System σ P Z)
        (left : Z → S) (right : Z → T) (z₀ : Z),
        PreservesEquations k g left ∧ PreservesEquations k h right ∧
          left z₀ = s ∧ right z₀ = t := by
  constructor
  · intro eq
    obtain ⟨R, sim, related⟩ := (least_eq_iff_bisim g h s t).1 eq
    obtain ⟨k, hl, hr⟩ := relation_span sim
    let : Fintype S := Fintype.ofFinite S
    let : Fintype T := Fintype.ofFinite T
    exact ⟨{st : S × T // R st.1 st.2}, Finite.of_injective Subtype.val Subtype.val_injective, k, _, _, ⟨(s, t), related⟩,
      hl, hr, rfl, rfl⟩
  · rintro ⟨Z, _, k, left, right, z₀, hl, hr, rfl, rfl⟩
    funext p
    exact (least_paths g (left z₀) p).trans ((paths_of_hom hl z₀ p).symm.trans
      ((paths_of_hom hr z₀ p).trans (least_paths h (right z₀) p).symm))

end Silmaril.Calco2019.Proofs.IterationObservations
