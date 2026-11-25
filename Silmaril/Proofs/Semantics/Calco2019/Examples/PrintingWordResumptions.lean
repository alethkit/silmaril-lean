module

public import Silmaril.Semantics.Calco2019.Examples.Printing.WordResumptions.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.WordResumptions.Proofs

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits

variable {A X Z S : Type u}

theorem parameter_map (f : X ⟶ Z) (t : S ⊕ (A × X)) :
    ((family A).toParametrizedMonad.parameter S).map f t = Sum.map id (Prod.map id f) t := by
  cases t <;> rfl

def foldHom (A X : Type u) (S : Algebra ((family A).toParametrizedMonad.parameter X)) :
    algebra A X ⟶ S where
  f := TypeCat.ofHom (fold S.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro t
    exact (congrArg (fun t => S.str t) (parameter_map (TypeCat.ofHom (fold S.str)) t)).trans
      (by rcases t with x | ⟨a, w, x⟩ <;> rfl)

noncomputable def initial (A X : Type u) : IsInitial (algebra A X) := by
  refine IsInitial.ofUniqueHom (foldHom A X) ?_
  intro S k
  apply Algebra.Hom.ext
  apply ConcreteCategory.hom_ext
  rintro ⟨w, x⟩
  change k.f (w, x) = fold S.str (w, x)
  have square (t : X ⊕ (A × (List A × X))) :
      S.str (Sum.map id (Prod.map id k.f) t) = k.f (roll t) :=
    (congrArg (fun t => S.str t) (parameter_map k.f t)).symm.trans
      (ConcreteCategory.congr_hom k.h t)
  induction w with
  | nil => exact (square (.inl x)).symm
  | cons a w ih =>
    have eq := (square (.inr (a, (w, x)))).symm
    change k.f (a :: w, x) = S.str (.inr (a, k.f (w, x))) at eq
    exact eq.trans (congrArg (fun s => S.str (.inr (a, s))) ih)

private theorem toHang_spec (t : Productive A X) :
    Hangs.observe (toHang t) = some (Sum.map id (Prod.map id toHang) (observe t)) := by
  rcases t with ⟨_ | _, _⟩ | stream
  · rfl
  · rfl
  · have eq : stream = Stream'.cons (stream 0) (fun i => stream (i + 1)) := by
      funext i
      cases i <;> rfl
    have h : Stream'.Seq.ofStream stream =
        Stream'.Seq.cons (stream 0) (Stream'.Seq.ofStream (fun i => stream (i + 1))) :=
      (congrArg Stream'.Seq.ofStream eq).trans (Stream'.Seq.ofStream_cons _ _)
    let lift : A × Stream'.Seq A → X ⊕ (A × Hangs.Model A X) :=
      fun (a, t) => .inr (a, .inr t)
    change (Stream'.Seq.ofStream stream).destruct.map lift =
      some (lift (stream 0, Stream'.Seq.ofStream (fun i => stream (i + 1))))
    exact congrArg (Option.map lift)
      ((congrArg Stream'.Seq.destruct h).trans (Stream'.Seq.destruct_cons _ _))

private theorem toHang_injective : Function.Injective (toHang (A := A) (X := X)) := by
  intro t u eq
  rcases t with t | t <;> rcases u with u | u
  · exact congrArg Sum.inl (Sum.inl.inj eq)
  · contradiction
  · contradiction
  · have h := Sum.inr.inj eq
    exact congrArg Sum.inr (funext fun n =>
      Option.some.inj (congrArg (fun s : Stream'.Seq A => s.get? n) h))

private theorem step_exists (f : S → X ⊕ (A × S))
    (s : {s // ¬ ∃ p : List A × X, Hangs.Returns (some ∘ f) s p.1 p.2}) :
    ∃ a : A, ∃ t : {s // ¬ ∃ p : List A × X, Hangs.Returns (some ∘ f) s p.1 p.2},
      f s.1 = .inr (a, t.1) := by
  cases e : f s.1 with
  | inl x => exact (s.2 ⟨([], x), .ret (congrArg some e)⟩).elim
  | inr at' =>
    obtain ⟨a, t⟩ := at'
    refine ⟨a, ⟨t, ?_⟩, rfl⟩
    rintro ⟨w, hw⟩
    exact s.2 ⟨(a :: w.1, w.2), .emit (congrArg some e) hw⟩

noncomputable def chooseStep (f : S → X ⊕ (A × S))
    (s : {s // ¬ ∃ p : List A × X, Hangs.Returns (some ∘ f) s p.1 p.2}) :=
  ((step_exists f s).choose, (step_exists f s).choose_spec.choose)

private theorem corec_productive (f : S → X ⊕ (A × S))
    (s : {s // ¬ ∃ p : List A × X, Hangs.Returns (some ∘ f) s p.1 p.2}) :
    Stream'.Seq.corec (strip f) s.1 = Stream'.Seq.ofStream (Stream'.corec' (chooseStep f) s) := by
  apply Stream'.Seq.eq_of_bisim'
    (fun p q => ∃ t, p = Stream'.Seq.corec (strip f) t.1 ∧
      q = Stream'.Seq.ofStream (Stream'.corec' (chooseStep f) t))
    ⟨s, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  have h := (step_exists f t).choose_spec.choose_spec
  refine .inr ⟨(chooseStep f t).1, Stream'.Seq.corec (strip f) (chooseStep f t).2.1,
    Stream'.Seq.ofStream (Stream'.corec' (chooseStep f) (chooseStep f t).2), ?_, ?_,
    (chooseStep f t).2, rfl, rfl⟩
  · apply Stream'.Seq.corec_cons
    exact congrArg (Sum.elim (fun _ => none) some) h
  · rw [Stream'.corec'_eq, Stream'.Seq.ofStream_cons]

noncomputable def unfold (f : S → X ⊕ (A × S)) (s : S) : Productive A X := by
  classical
  exact if h : ∃ r : List A × X, Hangs.Returns (some ∘ f) s r.1 r.2
    then .inl h.choose else .inr (Stream'.corec' (chooseStep f) ⟨s, h⟩)

theorem unfold_toHang (f : S → X ⊕ (A × S)) (s : S) :
    toHang (unfold f s) = Hangs.unfoldTrace (some ∘ f) s := by
  classical
  unfold unfold
  split
  · rename_i h
    exact (Hangs.unfoldTrace_return h.choose_spec).symm
  · rename_i h
    unfold Hangs.unfoldTrace
    rw [dite_eq_right h]
    exact congrArg Sum.inr (corec_productive f ⟨s, h⟩).symm

theorem unfold_spec (f : S → X ⊕ (A × S)) (s : S) :
    observe (unfold f s) = Sum.map id (Prod.map id (unfold f)) (f s) := by
  have eq := Hangs.unfoldTrace_spec (some ∘ f) s
  rw [← unfold_toHang, toHang_spec] at eq
  change some (Sum.map id (Prod.map id toHang) (observe (unfold f s))) =
    Hangs.layerMap (Hangs.unfoldTrace (some ∘ f)) (some (f s)) at eq
  cases h : f s with
  | inl x =>
    rw [h] at eq
    have eq' : Sum.map id (Prod.map id toHang) (observe (unfold f s)) = Sum.inl x := Option.some.inj eq
    cases o : observe (unfold f s) <;> rw [o] at eq'
    · exact congrArg Sum.inl (Sum.inl.inj eq')
    · contradiction
  | inr t =>
    obtain ⟨a, s'⟩ := t
    rw [h] at eq
    have eq' : Sum.map id (Prod.map id toHang) (observe (unfold f s)) =
        Sum.inr (a, Hangs.unfoldTrace (some ∘ f) s') := Option.some.inj eq
    rw [← unfold_toHang] at eq'
    cases o : observe (unfold f s) with
    | inl x => rw [o] at eq'; contradiction
    | inr t =>
      obtain ⟨b, r⟩ := t
      rw [o] at eq'
      have d := Prod.mk.inj (Sum.inr.inj eq')
      exact congrArg Sum.inr (Prod.ext d.1 (toHang_injective d.2))

theorem unfold_unique (f : S → X ⊕ (A × S)) (g : S → Productive A X)
    (h : ∀ s, observe (g s) = Sum.map id (Prod.map id g) (f s)) : g = unfold f := by
  have eq := Hangs.unfoldTrace_unique (some ∘ f) (toHang ∘ g) (fun s => by
    change Hangs.observe (toHang (g s)) = _
    rw [toHang_spec, h]
    change some (Sum.map id (Prod.map id toHang) (Sum.map id (Prod.map id g) (f s))) =
      Hangs.layerMap (toHang ∘ g) (some (f s))
    cases f s <;> rfl)
  funext s
  exact toHang_injective ((congrFun eq s).trans (unfold_toHang f s).symm)

noncomputable def unfoldHom (A X : Type u) (S : Coalgebra ((family A).toParametrizedMonad.parameter X)) :
    S ⟶ coalgebra A X where
  f := TypeCat.ofHom (unfold S.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (parameter_map (TypeCat.ofHom (unfold S.str)) (S.str s)).trans (unfold_spec S.str s).symm

noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) := by
  refine IsTerminal.ofUniqueHom (unfoldHom A X) ?_
  intro S k
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro s
  exact congrFun (unfold_unique S.str k.f (fun t =>
    (ConcreteCategory.congr_hom k.h t).symm.trans (parameter_map k.f (S.str t)))) s

end Silmaril.Calco2019.Examples.Printing.WordResumptions.Proofs
