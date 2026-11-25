module

public import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.MatrixTrace.Defs
import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Boundary.Thms
import Silmaril.Semantics.Calco2019.Trace.CounterSemiring.Stages.Thms
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

public section

set_option backward.isDefEq.respectTransparency false

universe u

namespace Silmaril.Calco2019.Proofs.CounterSemiringMatrixTrace

open CategoryTheory CategoryTheory.Limits Guardedness
open Silmaril.Calco2019.CounterSemiring
open FiniteMatrix


@[simp] private theorem inl_eq (X Y : Object) :
    coproducts.inl (X := X) (Y := Y) = relabel Sum.inl := rfl

@[simp] private theorem inr_eq (X Y : Object) :
    coproducts.inr (X := X) (Y := Y) = relabel Sum.inr := rfl

private theorem map_apply {A B C D : Object} (f : A ⟶ C) (g : B ⟶ D)
    (x : A.carrier ⊕ B.carrier) (y : C.carrier ⊕ D.carrier) :
    coproducts.map f g x y = match x, y with
      | .inl a, .inl c => f a c
      | .inr b, .inr d => g b d
      | _, _ => 0 := by
  cases x <;> cases y <;> simp [Coproducts.map, comp_relabel]
  · rename_i a c
    change (∑ y : C.carrier, if (Sum.inl y : C.carrier ⊕ D.carrier) = .inl c then f a y else 0) = f a c
    simp
  · rename_i b d
    change (∑ y : D.carrier, if (Sum.inr y : C.carrier ⊕ D.carrier) = .inr d then g b y else 0) = g b d
    simp

private theorem pre_apply {A B U A' : Object} (a : A' ⟶ A)
    (f : coproducts.sum A U ⟶ coproducts.sum B U) :
    (fun x y => (coproducts.map a (𝟙 U) ≫ f) x y) = preBoundary a (fun x y => f x y) := by
  funext x y
  rw [FiniteMatrix.comp_apply]
  change (∑ j : A.carrier ⊕ U.carrier, coproducts.map a (𝟙 U) x j * f j y) = _
  rw [Fintype.sum_sum_type]
  cases x <;> simp [map_apply, preBoundary, ite_mul]

private theorem post_apply {A B U B' : Object} (b : B ⟶ B')
    (f : coproducts.sum A U ⟶ coproducts.sum B U) :
    (fun x y => (f ≫ coproducts.map b (𝟙 U)) x y) = postBoundary b (fun x y => f x y) := by
  funext x y
  rw [FiniteMatrix.comp_apply]
  change (∑ j : B.carrier ⊕ U.carrier, f x j * coproducts.map b (𝟙 U) j y) = _
  rw [Fintype.sum_sum_type]
  cases y <;> simp [map_apply, postBoundary, mul_ite]

theorem tighten_eq {A B U A' B' : Object} (f : coproducts.sum A U ⟶ coproducts.sum B U)
    (a : A' ⟶ A) (b : B ⟶ B') (h : (Guardedness.greatest coproducts).FeedbackGuard f) :
    (feedback (tighten f a b) (tighten_feedbackGuard f a b h) : A' ⟶ B') =
      a ≫ feedback f h ≫ b := by
  apply Matrix.ext
  intro x y
  change networkFeedback (fun i j => (coproducts.map a (𝟙 U) ≫ (f ≫ coproducts.map b (𝟙 U))) i j) x y = _
  refine (congrArg (fun f : Network A'.carrier B'.carrier U.carrier => networkFeedback f x y)
    (pre_apply (A := A) (B := B') a (f ≫ coproducts.map b (𝟙 U)))).trans ?_
  have p := congrArg (preBoundary (U := U.carrier) a) (post_apply (A := A) (B := B) b f)
  refine (congrArg (fun f : Network A'.carrier B'.carrier U.carrier => networkFeedback f x y) p).trans ?_
  change eliminateStates Finset.univ (preBoundary a (postBoundary b (fun i j => f i j))) (.inl x) (.inl y) = _
  rw [eliminateStates_preBoundary, eliminateStates_postBoundary]
  simp [preBoundary, postBoundary, FiniteMatrix.comp_apply, feedback, networkFeedback, Finset.mul_sum]

private theorem slide_after {A B U V : Object} (f : coproducts.sum A U ⟶ coproducts.sum B V) (q : V ⟶ U) :
    (fun x y => (f ≫ coproducts.map (𝟙 B) q) x y) = slidingAfter f q := by
  funext x y
  rw [FiniteMatrix.comp_apply]
  change (∑ j : B.carrier ⊕ V.carrier, f x j * coproducts.map (𝟙 B) q j y) = _
  rw [Fintype.sum_sum_type]
  cases y <;> simp [map_apply, slidingAfter, mul_ite]

private theorem slide_before {A B U V : Object} (f : coproducts.sum A U ⟶ coproducts.sum B V) (q : V ⟶ U) :
    (fun x y => (coproducts.map (𝟙 A) q ≫ f) x y) = slidingBefore f q := by
  funext x y
  rw [FiniteMatrix.comp_apply]
  change (∑ j : A.carrier ⊕ U.carrier, coproducts.map (𝟙 A) q x j * f j y) = _
  rw [Fintype.sum_sum_type]
  cases x <;> simp [map_apply, slidingBefore, ite_mul]

theorem slide_eq {A B U V : Object} (f : coproducts.sum A U ⟶ coproducts.sum B V) (q : V ⟶ U) :
    (feedback (f ≫ coproducts.map (𝟙 B) q) True.intro : A ⟶ B) =
      feedback (coproducts.map (𝟙 A) q ≫ f) True.intro := by
  apply Matrix.ext
  intro x y
  change networkFeedback (fun i j => (f ≫ coproducts.map (𝟙 B) q) i j) x y =
    networkFeedback (fun i j => (coproducts.map (𝟙 A) q ≫ f) i j) x y
  exact (congrArg (fun f : Network A.carrier B.carrier U.carrier => networkFeedback f x y)
    (slide_after (A := A) (B := B) f q)).trans
    ((congrArg (fun f => f x y) (networkFeedback_slide (fun i j => f i j) q)).trans
      (congrArg (fun f : Network A.carrier B.carrier V.carrier => networkFeedback f x y)
        (slide_before (A := A) (B := B) f q)).symm)

theorem vanish_initial_eq {A B I : Object} (i : IsInitial I) (f : coproducts.sum A I ⟶ coproducts.sum B I) :
    (feedback f True.intro : A ⟶ B) = coproducts.inl ≫ f ≫ coproducts.desc (𝟙 B) (i.to B) := by
  let : IsEmpty I.carrier := isEmpty_of_initial i
  apply Matrix.ext
  intro x y
  change networkFeedback (fun a b => f a b) x y = (relabel Sum.inl ≫ f ≫ coproducts.desc (𝟙 B) (i.to B)) x y
  rw [relabel_comp (X := A) (Y := sum A I) Sum.inl _ x y, FiniteMatrix.comp_apply]
  change eliminateStates (Finset.univ : Finset I.carrier) (fun a b => f a b) (.inl x) (.inl y) =
    ∑ j : B.carrier ⊕ I.carrier, f (.inl x) j * coproducts.desc (𝟙 B) (i.to B) j y
  rw [Fintype.sum_sum_type]
  simp [eliminateStates, mul_ite]
  rfl

theorem yank_eq (U : Object) : (feedback (coproducts.swap (X := U) (Y := U)) True.intro : U ⟶ U) = 𝟙 U := by
  let f : Network U.carrier U.carrier U.carrier := fun x y => coproducts.swap (X := U) (Y := U) x y
  have noEdges : ∀ i ∈ (Finset.univ : Finset U.carrier), ∀ j ∈ (Finset.univ : Finset U.carrier),
      f (.inr i) (.inr j) = 0 := by
    intro i _ j _
    change coproducts.swap (X := U) (Y := U) (.inr i) (.inr j) = 0
    simp [Coproducts.swap, relabel]
  apply Matrix.ext
  intro x y
  change eliminateStates Finset.univ f (.inl x) (.inl y) = _
  rw [eliminateStates_noInternalEdges _ _ noEdges]
  simp [f, Coproducts.swap, relabel]
  change (∑ z : U.carrier, if (Sum.inl z : U.carrier ⊕ U.carrier) = .inl y then
    if (Sum.inr x : U.carrier ⊕ U.carrier) = .inr z then (1 : Scalar) else 0 else 0) = _
  simp

private theorem relabel_chain {A B C : Object} (f : A.carrier → B.carrier) (g : B.carrier → C.carrier) :
    relabel (X := A) (Y := B) f ≫ relabel (X := B) (Y := C) g =
      relabel (X := A) (Y := C) (g ∘ f) := by
  apply Matrix.ext
  intro x y
  exact relabel_comp (X := A) (Y := B) f (relabel g) x y

private theorem assoc_eq (A U V : Object) :
    coproducts.assoc (X := A) (Y := U) (Z := V) =
      relabel (X := sum (sum A U) V) (Y := sum A (sum U V))
        (Equiv.sumAssoc A.carrier U.carrier V.carrier) := by
  apply Matrix.ext
  intro x y
  rcases x with (a | u) | v <;>
    simp only [Coproducts.assoc, desc_inl_apply, desc_inr_apply, inl_eq, inr_eq, relabel_chain]
  all_goals rfl

private theorem comp_equiv {A B C : Object} (f : A ⟶ B) (e : B.carrier ≃ C.carrier)
    (x : A.carrier) (y : C.carrier) :
    (f ≫ relabel (X := B) (Y := C) e) x y = f x (e.symm y) := by
  rw [comp_relabel]
  have eq (j : B.carrier) : e j = y ↔ j = e.symm y := by
    constructor
    · intro h
      exact e.injective (h.trans (e.apply_symm_apply y).symm)
    · intro h
      rw [h, e.apply_symm_apply]
  simp only [eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem vanish_pair_eq {A B U V : Object}
    (s : TwoStateBody (Guardedness.greatest coproducts) A B U V) :
    Feedback.onBranches feedback (s.entry ≫ coproducts.assoc)
      (coproducts.desc s.first s.second ≫ coproducts.assoc) True.intro =
    feedback (Feedback.onBranches feedback (coproducts.desc s.entry s.first) s.second True.intro)
      True.intro := by
  let joint := coproducts.desc (s.entry ≫ coproducts.assoc)
    (coproducts.desc s.first s.second ≫ coproducts.assoc)
  let nested := coproducts.desc (coproducts.desc s.entry s.first) s.second
  have body : innerBody (fun x y => joint x y) = fun x y => nested x y := by
    funext x y
    rcases x with (a | u) | v
    all_goals simp only [innerBody, joint, nested, Equiv.sumAssoc_apply_inl_inl,
      Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr,
      desc_inl_apply (X := A) (Y := sum U V) (Z := sum B (sum U V)),
      desc_inr_apply (X := A) (Y := sum U V) (Z := sum B (sum U V)),
      desc_inl_apply (X := sum A U) (Y := V) (Z := sum (sum B U) V),
      desc_inr_apply (X := sum A U) (Y := V) (Z := sum (sum B U) V),
      desc_inl_apply (X := A) (Y := U) (Z := sum (sum B U) V),
      desc_inr_apply (X := A) (Y := U) (Z := sum (sum B U) V),
      assoc_eq]
    · exact (comp_equiv (B := sum (sum B U) V) (C := sum B (sum U V)) s.entry
        (Equiv.sumAssoc B.carrier U.carrier V.carrier) a _).trans
        (congrArg (s.entry a) (Equiv.symm_apply_apply _ _))
    · refine (comp_equiv (B := sum (sum B U) V) (C := sum B (sum U V))
        (coproducts.desc s.first s.second) (Equiv.sumAssoc B.carrier U.carrier V.carrier)
        (.inl u) _).trans ?_
      exact (congrArg (fun z => coproducts.desc s.first s.second (.inl u) z)
        (Equiv.symm_apply_apply (Equiv.sumAssoc B.carrier U.carrier V.carrier) y)).trans
        (desc_inl_apply s.first s.second u y)
    · refine (comp_equiv (B := sum (sum B U) V) (C := sum B (sum U V))
        (coproducts.desc s.first s.second) (Equiv.sumAssoc B.carrier U.carrier V.carrier)
        (.inr v) _).trans ?_
      exact (congrArg (fun z => coproducts.desc s.first s.second (.inr v) z)
        (Equiv.symm_apply_apply (Equiv.sumAssoc B.carrier U.carrier V.carrier) y)).trans
        (desc_inr_apply s.first s.second v y)
  have eq := networkFeedback_vanishPair (A := A.carrier) (B := B.carrier)
    (U := U.carrier) (V := V.carrier) (fun x y => joint x y)
  rw [body] at eq
  apply Matrix.ext
  intro x y
  exact (congrArg (fun f => f x y) eq).symm

private theorem intoLeft {A B D : Object} (f : A ⟶ B) (x : A.carrier) (y : B.carrier ⊕ D.carrier) :
    (f ≫ coproducts.inl (X := B) (Y := D)) x y = y.elim (f x) (fun _ => 0) := by
  rw [inl_eq, comp_relabel]
  change (∑ j : B.carrier, if (Sum.inl j : B.carrier ⊕ D.carrier) = y then f x j else 0) = _
  cases y <;> simp

private theorem intoRight {A B D : Object} (f : A ⟶ D) (x : A.carrier) (y : B.carrier ⊕ D.carrier) :
    (f ≫ coproducts.inr (X := B) (Y := D)) x y = y.elim (fun _ => 0) (f x) := by
  rw [inr_eq, comp_relabel]
  change (∑ j : D.carrier, if (Sum.inr j : B.carrier ⊕ D.carrier) = y then f x j else 0) = _
  cases y <;> simp

private theorem post_left {A B U B' : Object} (f : coproducts.sum A U ⟶ coproducts.sum B U)
    (x : A.carrier ⊕ U.carrier) (y : (B.carrier ⊕ B'.carrier) ⊕ U.carrier) :
    (f ≫ coproducts.map (coproducts.inl (X := B) (Y := B')) (𝟙 U)) x y =
      match y with
      | .inl (.inl j) => f x (.inl j)
      | .inl (.inr _) => 0
      | .inr j => f x (.inr j) := by
  refine (congrArg (fun h : Network A.carrier (B.carrier ⊕ B'.carrier) U.carrier => h x y)
    (post_apply (A := A) (B := B) (B' := sum B B') coproducts.inl f)).trans ?_
  rcases y with (j | j) | j
  · change (∑ k : B.carrier, f x (.inl k) *
      (if (Sum.inl k : B.carrier ⊕ B'.carrier) = .inl j then (1 : Scalar) else 0)) = _
    simp [mul_ite]
  · change (∑ k : B.carrier, f x (.inl k) *
      (if (Sum.inl k : B.carrier ⊕ B'.carrier) = .inr j then (1 : Scalar) else 0)) = _
    simp
  · rfl

private theorem beside_apply {A B U A' B' : Object} (f : coproducts.sum A U ⟶ coproducts.sum B U)
    (g : A' ⟶ B') (x : (A.carrier ⊕ A'.carrier) ⊕ U.carrier)
    (y : (B.carrier ⊕ B'.carrier) ⊕ U.carrier) :
    superpose (P := coproducts) f g x y =
      match x, y with
      | .inl (.inl i), .inl (.inl j) => f (.inl i) (.inl j)
      | .inl (.inl i), .inr j => f (.inl i) (.inr j)
      | .inr i, .inl (.inl j) => f (.inr i) (.inl j)
      | .inr i, .inr j => f (.inr i) (.inr j)
      | .inl (.inr i), .inl (.inr j) => g i j
      | _, _ => 0 := by
  rcases x with (i | i) | i
  all_goals simp only [superpose,
    desc_inl_apply (X := sum A A') (Y := U) (Z := sum (sum B B') U),
    desc_inr_apply (X := sum A A') (Y := U) (Z := sum (sum B B') U),
    desc_inl_apply (X := A) (Y := A') (Z := sum (sum B B') U),
    desc_inr_apply (X := A) (Y := A') (Z := sum (sum B B') U)]
  · exact (relabel_comp (X := A) (Y := sum A U) Sum.inl
      (f ≫ coproducts.map (coproducts.inl (X := B) (Y := B')) (𝟙 U)) i y).trans
      (by rcases y with (j | j) | j <;> exact post_left (A := A) (B := B) (B' := B') f _ _)
  · rw [← Category.assoc]
    rcases y with (j | j) | j
    · exact (intoLeft (g ≫ coproducts.inr (X := B) (Y := B')) i (.inl (.inl j))).trans
        (intoRight g i (.inl j))
    · exact (intoLeft (g ≫ coproducts.inr (X := B) (Y := B')) i (.inl (.inr j))).trans
        (intoRight g i (.inr j))
    · exact intoLeft (g ≫ coproducts.inr (X := B) (Y := B')) i (.inr j)
  · exact (relabel_comp (X := U) (Y := sum A U) Sum.inr
      (f ≫ coproducts.map (coproducts.inl (X := B) (Y := B')) (𝟙 U)) i y).trans
      (by rcases y with (j | j) | j <;> exact post_left (A := A) (B := B) (B' := B') f _ _)

theorem superpose_eq {A B U A' B' : Object} (f : coproducts.sum A U ⟶ coproducts.sum B U)
    (g : A' ⟶ B') (h : (Guardedness.greatest coproducts).FeedbackGuard f) :
    (feedback (superpose f g) (superpose_feedbackGuard f g h) :
      coproducts.sum A A' ⟶ coproducts.sum B B') = coproducts.map (feedback f h) g := by
  let f' : Network (A.carrier ⊕ A'.carrier) (B.carrier ⊕ B'.carrier) U.carrier := fun x y => superpose f g x y
  let row : A.carrier ⊕ U.carrier → (A.carrier ⊕ A'.carrier) ⊕ U.carrier := Sum.map Sum.inl id
  let col : B.carrier ⊕ U.carrier → (B.carrier ⊕ B'.carrier) ⊕ U.carrier := Sum.map Sum.inl id
  have restrict : (fun x y => f' (row x) (col y)) = fun x y => f x y := by
    funext x y
    cases x <;> cases y <;> exact beside_apply (A := A) (B := B) f g _ _
  have main := eliminateStates_reindex (A' := A.carrier) (B' := B.carrier) Finset.univ
    (Function.Embedding.refl U.carrier) row col (fun _ => rfl) (fun _ => rfl) f'
  rw [restrict, Finset.map_refl] at main
  have rows (x : A'.carrier) : ∀ u ∈ (Finset.univ : Finset U.carrier), f' (.inl (.inr x)) (.inr u) = 0 :=
    fun u _ => beside_apply (A := A) (B := B) f g _ _
  have cols (y : B'.carrier) : ∀ u ∈ (Finset.univ : Finset U.carrier), f' (.inr u) (.inl (.inr y)) = 0 :=
    fun u _ => beside_apply (A := A) (B := B) f g _ _
  apply Matrix.ext
  intro x y
  refine Eq.trans ?_ (map_apply (feedback f h) g x y).symm
  change eliminateStates Finset.univ f' (.inl x) (.inl y) = _
  rcases x with x | x <;> rcases y with y | y
  · exact (congrArg (fun k : Network A.carrier B.carrier U.carrier => k (.inl x) (.inl y)) main).symm
  · exact (eliminateStates_isolatedOutput _ f' _ (cols y) _).trans
      (beside_apply (A := A) (B := B) f g _ _)
  · exact (eliminateStates_isolatedInput _ f' _ (rows x) _).trans
      (beside_apply (A := A) (B := B) f g _ _)
  · exact (eliminateStates_isolatedInput _ f' _ (rows x) _).trans
      (beside_apply (A := A) (B := B) f g _ _)

end Silmaril.Calco2019.Proofs.CounterSemiringMatrixTrace
