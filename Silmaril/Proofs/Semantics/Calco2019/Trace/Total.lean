module

public import Silmaril.Semantics.Calco2019.Trace.Total.Defs
import Silmaril.Proofs.Semantics.Calco2019.Trace.Converse
import Silmaril.Proofs.Semantics.Calco2019.Trace.Profile

public section

universe u v

namespace Silmaril.Calco2019.Proofs.Feedback

open CategoryTheory CategoryTheory.Limits Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K}

variable {tr : Guardedness.Feedback (Guardedness.greatest P)}

private theorem close_acyclic (laws : Feedback.JoyalStreetVerity (P := P) tr) {A B U : K} (entry : A ⟶ P.sum B U) (k : U ⟶ B) :
    Feedback.onBranches (G := Guardedness.greatest P) tr entry (k ≫ P.inl) True.intro = entry ≫ P.desc (𝟙 B) k := by
  let sw := P.swap (X := U) (Y := U)
  let f := superpose sw (𝟙 B)
  let a := entry ≫ P.swap
  let b := P.desc k (𝟙 B)
  have e : tighten f a b = P.desc entry (k ≫ P.inl) := by
    apply P.hom_ext <;> simp [tighten, f, sw, a, b, superpose, Coproducts.map, Coproducts.swap]
  have h₁ : tr (tighten f a b) True.intro = a ≫ tr f True.intro ≫ b :=
    laws.tighten f a b True.intro
  have h₂ : tr f True.intro = P.map (tr sw True.intro) (𝟙 B) :=
    laws.superpose sw (𝟙 B) True.intro
  refine (trace_eq (G := Guardedness.greatest P) e.symm _ True.intro).trans (h₁.trans ?_)
  rw [h₂, laws.yank U]
  simp [a, b, Coproducts.swap, Coproducts.map]

theorem total_slide_shared (laws : Feedback.JoyalStreetVerity (P := P) tr) {A B U V : K} (f : P.sum A U ⟶ P.sum B V) (h : V ⟶ P.sum B U) :
    tr (slideAfter f h) True.intro = tr (slideBefore f h) True.intro := by
  let j : P.sum B V ⟶ P.sum (P.sum B U) V := P.map P.inl (𝟙 V)
  let k : P.sum B U ⟶ P.sum (P.sum B V) U := P.map P.inl (𝟙 U)
  let s : TwoStateBody (Guardedness.greatest P) A B U V :=
    ⟨P.inl ≫ f ≫ j, P.inr ≫ f ≫ j, h ≫ P.inl, True.intro⟩
  let t : TwoStateBody (Guardedness.greatest P) A B V U :=
    ⟨P.inl ≫ f ≫ P.inl, h ≫ k, (P.inr ≫ f) ≫ P.inl, True.intro⟩
  let sf := P.desc (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc)
  let tf := P.desc (t.entry ≫ P.assoc) (P.desc t.first t.second ≫ P.assoc)
  let g := sf ≫ P.map (𝟙 B) (P.swap (X := U) (Y := V))
  let swap := P.swap (X := V) (Y := U)
  have e₁ : g ≫ P.map (𝟙 B) swap = sf := by
    have cancel : P.map (𝟙 B) (P.swap (X := U) (Y := V)) ≫ P.map (𝟙 B) swap = 𝟙 _ := by
      apply P.hom_ext
      · simp [Coproducts.map]
      · apply P.hom_ext <;> simp [swap, Coproducts.map, Coproducts.swap]
    dsimp only [g]
    rw [Category.assoc, cancel, Category.comp_id]
  have e₂ : P.map (𝟙 A) swap ≫ g = tf := by
    apply P.hom_ext
    · simp [g, sf, tf, s, t, j, Coproducts.map, Coproducts.assoc, Coproducts.swap]
    · apply P.hom_ext <;> simp [g, sf, tf, s, t, j, k, swap, Coproducts.map,
        Coproducts.assoc, Coproducts.swap]
  have balance : tr sf True.intro = tr tf True.intro :=
    (trace_eq (G := Guardedness.greatest P) e₁.symm True.intro True.intro).trans ((laws.slide g swap).trans (trace_eq (G := Guardedness.greatest P) e₂ True.intro True.intro))
  have close_s : Feedback.onBranches (G := Guardedness.greatest P) tr (P.desc s.entry s.first) s.second True.intro =
      slideAfter f h := by
    refine (close_acyclic laws _ h).trans ?_
    apply P.hom_ext <;> simp [slideAfter, s, j]
  have close_t : Feedback.onBranches (G := Guardedness.greatest P) tr (P.desc t.entry t.first) t.second True.intro =
      slideBefore f h := by
    refine (close_acyclic laws _ (P.inr ≫ f)).trans ?_
    apply P.hom_ext <;> simp [slideBefore, t, k]
  exact (trace_eq (G := Guardedness.greatest P) close_s.symm True.intro True.intro).trans ((laws.vanishPair s).symm.trans
    (balance.trans ((laws.vanishPair t).trans (trace_eq (G := Guardedness.greatest P) close_t True.intro True.intro))))

private theorem total_inner_formula [HasInitial K] (loc : Feedback.LocalLaws tr)
    {A B U V : K} (s : TwoStateBody (Guardedness.greatest P) A B U V) :
    let finish := P.desc (𝟙 (P.sum B U)) (Feedback.iterate tr s.second s.second_guard)
    Feedback.onBranches tr (P.desc s.entry s.first) s.second s.second_guard =
      P.desc (s.entry ≫ finish) (s.first ≫ finish) :=
  (Feedback.onBranches_formula loc _ _ s.second_guard).trans (P.desc_comp _ _ _)

theorem total_pair_iff [HasInitial K] (loc : Feedback.LocalLaws tr) :
    Feedback.PairVanishing tr ↔
      ∀ {A B U V : K} (s : TwoStateBody (Guardedness.greatest P) A B U V),
        Feedback.onBranches tr (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc) True.intro =
          tr (Feedback.onBranches tr (P.desc s.entry s.first) s.second True.intro) True.intro := by
  constructor
  · intro hp A B U V s
    exact (hp s True.intro).trans
      (trace_eq (G := Guardedness.greatest P) (total_inner_formula loc s).symm True.intro True.intro)
  · intro hp A B U V s h
    exact (hp s).trans
      (trace_eq (G := Guardedness.greatest P) (total_inner_formula loc s) True.intro True.intro)

theorem total_ofConway [HasInitial K] (F : (Guardedness.greatest P).Conway) :
    Feedback.JoyalStreetVerity F.toFixpoints.feedback where
  tighten := feedback_tighten F
  superpose := feedback_superpose F
  slide f q := feedback_slide F f q (Or.inl True.intro)
  vanishInitial := feedback_vanish_initial F.toFixpoints
  vanishPair := (total_pair_iff (Feedback.localLaws_ofConway F)).1
    (Feedback.lawful_ofConway F).vanishPair
  yank := feedback_yank F.toFixpoints

theorem total_of_lawful [HasInitial K] (laws : Feedback.Lawful tr) :
    Feedback.JoyalStreetVerity tr := by
  have h := total_ofConway (Feedback.conway laws)
  have e : @Eq (Guardedness.Feedback (Guardedness.greatest P))
      (Feedback.conway laws).toFixpoints.feedback tr := by
    funext A B U f hf
    exact Feedback.fixpoints_feedback laws.toLocalLaws f hf
  exact e ▸ h

theorem total_pair_body (laws : Feedback.JoyalStreetVerity tr) {A B U V : K}
    (f : P.sum A (P.sum U V) ⟶ P.sum B (P.sum U V)) :
    let s := Feedback.splitTotalBody f
    tr f True.intro =
      tr (Feedback.onBranches (G := Guardedness.greatest P) tr
        (P.desc s.entry s.first) s.second True.intro) True.intro := by
  let s := Feedback.splitTotalBody f
  have e : P.desc (s.entry ≫ P.assoc) (P.desc s.first s.second ≫ P.assoc) = f := by
    apply P.hom_ext
    · simp [s, Feedback.splitTotalBody, assocInv_assoc]
    · apply P.hom_ext <;> simp [s, Feedback.splitTotalBody, assocInv_assoc]
  exact (trace_eq (G := Guardedness.greatest P) e.symm True.intro True.intro).trans (laws.vanishPair s)

end Silmaril.Calco2019.Proofs.Feedback
