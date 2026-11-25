module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Hangs.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Hangs.Proofs

variable {A X S : Type u}

theorem observe_emit (a : A) (t : Model A X) :
    observe (emit a t) = some (.inr (a, t)) := by
  rcases t with ⟨w, x⟩ | s
  · rfl
  · simp [emit, observe, Option.map]

theorem observe_injective : Function.Injective (observe (A := A) (X := X)) := by
  let rebuild : Layer A X (Model A X) → Model A X
    | none => .inr Stream'.Seq.nil
    | some (.inl x) => .inl ([], x)
    | some (.inr (a, t)) => emit a t
  have h : ∀ t, rebuild (observe t) = t := by
    rintro (⟨_ | _, x⟩ | seq)
    · rfl
    · rfl
    · induction seq using Stream'.Seq.recOn <;> simp [rebuild, observe, emit, Option.map]
  exact Function.LeftInverse.injective h

private theorem returns_unique {body : S → Layer A X S} {s : S} {w : List A} {x : X}
    (h : Returns body s w x) {v : List A} {y : X} (h' : Returns body s v y) :
    (w, x) = (v, y) := by
  induction h generalizing v y with
  | ret h =>
    cases h' with
    | ret h' => cases h.symm.trans h'; rfl
    | emit h' _ => cases h.symm.trans h'
  | emit h _ ih =>
    cases h' with
    | ret h' => cases h.symm.trans h'
    | emit h' tail =>
      cases h.symm.trans h'
      cases ih tail
      rfl

theorem unfoldTrace_return {body : S → Layer A X S} {s : S} {w : List A} {x : X}
    (h : Returns body s w x) : unfoldTrace body s = .inl (w, x) := by
  unfold unfoldTrace
  have h' : ∃ r : List A × X, Returns body s r.1 r.2 := ⟨(w, x), h⟩
  rw [dite_eq_left h']
  exact congrArg Sum.inl (returns_unique h'.choose_spec h)

theorem unfoldTrace_hang {body : S → Layer A X S} {s : S}
    (h : ¬ ∃ r : List A × X, Returns body s r.1 r.2) :
    unfoldTrace body s = .inr (Stream'.Seq.corec (printingOnly ∘ body) s) := dite_eq_right h

theorem unfoldTrace_spec (body : S → Layer A X S) (s : S) :
    observe (unfoldTrace body s) = layerMap (unfoldTrace body) (body s) := by
  cases hs : body s with
  | none =>
    have noReturn : ¬ ∃ r : List A × X, Returns body s r.1 r.2 := by
      rintro ⟨⟨w, x⟩, h⟩
      cases h <;> simp_all
    simp [unfoldTrace_hang noReturn, observe, layerMap, hs, printingOnly, Stream'.Seq.omap, Option.map, Option.bind]
  | some t =>
    cases t with
    | inl x => rw [unfoldTrace_return (Returns.ret hs)]; rfl
    | inr p =>
      obtain ⟨a, t⟩ := p
      by_cases h : ∃ r : List A × X, Returns body t r.1 r.2
      · obtain ⟨⟨w, x⟩, tail⟩ := h
        have whole := Returns.emit hs tail
        simp [unfoldTrace_return tail, unfoldTrace_return whole, observe, layerMap, Option.map]
      · have noReturn : ¬ ∃ r : List A × X, Returns body s r.1 r.2 := by
          rintro ⟨⟨w, x⟩, run⟩
          cases run with
          | ret stop => cases hs.symm.trans stop
          | emit step tail =>
            cases hs.symm.trans step
            exact h ⟨(_, x), tail⟩
        simp [unfoldTrace_hang h, unfoldTrace_hang noReturn, observe, layerMap, hs,
          printingOnly, Stream'.Seq.omap, Option.map, Option.bind]

private theorem output_observe (t : Model A X) :
    (output t).destruct = Stream'.Seq.omap output (printingOnly (observe t)) := by
  rcases t with ⟨_ | _, x⟩ | s
  · rfl
  · simp [output, observe, printingOnly, Stream'.Seq.omap, Option.bind]
    rfl
  · cases h : s.destruct with
    | none =>
      simp [output, observe, printingOnly, h, Option.map, Option.bind]
      rfl
    | some p =>
      cases p
      simp [output, observe, printingOnly, h, Stream'.Seq.omap, Option.map, Option.bind]
      rfl

private theorem output_unique (body : S → Layer A X S) (k : S → Model A X)
    (hk : ∀ s, observe (k s) = layerMap k (body s)) (s : S) :
    output (k s) = Stream'.Seq.corec (printingOnly ∘ body) s := by
  apply Stream'.Seq.eq_of_bisim (fun p q => ∃ t, p = output (k t) ∧ q = Stream'.Seq.corec (printingOnly ∘ body) t)
    ?_ ⟨s, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  rw [output_observe, hk, Stream'.Seq.corec_eq]
  cases h : body t with
  | none => simp [h, layerMap, printingOnly, Stream'.Seq.omap, Option.map, Option.bind]
  | some layer =>
    rcases layer with x | ⟨a, next⟩
    · simp [h, layerMap, printingOnly, Stream'.Seq.omap, Option.map, Option.bind]
    · simp only [Function.comp_apply, h, layerMap, printingOnly, Option.map, Option.bind,
        Sum.map, Prod.map, Sum.elim, Stream'.Seq.omap, Stream'.Seq.BisimO]
      exact ⟨rfl, ⟨next, rfl, rfl⟩⟩

private theorem returns_of_model (body : S → Layer A X S) (k : S → Model A X)
    (hk : ∀ s, observe (k s) = layerMap k (body s))
    {w : List A} {s : S} {x : X} (h : k s = .inl (w, x)) : Returns body s w x := by
  induction w generalizing s with
  | nil =>
    have eq := (congrArg observe h).symm.trans (hk s)
    cases hs : body s with
    | none => simp [hs, layerMap, observe] at eq
    | some l =>
      cases l with
      | inl y =>
        have e : x = y := by simpa [hs, layerMap, observe] using eq
        exact .ret (e ▸ hs)
      | inr p => simp [hs, layerMap, observe] at eq
  | cons a w ih =>
    have eq := (congrArg observe h).symm.trans (hk s)
    cases hs : body s with
    | none => simp [hs, layerMap, observe] at eq
    | some l =>
      rcases l with y | ⟨a', t⟩
      · simp [hs, layerMap, observe] at eq
      · have e : a = a' ∧ (Sum.inl (w, x) : Model A X) = k t := by
          simpa [hs, layerMap, observe] using eq
        exact .emit (e.1 ▸ hs) (ih e.2.symm)

private theorem model_of_returns {body : S → Layer A X S} {k : S → Model A X}
    (hk : ∀ s, observe (k s) = layerMap k (body s)) {s : S} {w : List A} {x : X}
    (h : Returns body s w x) : k s = .inl (w, x) := by
  induction h with
  | ret ret =>
    apply observe_injective
    rw [hk, ret]
    rfl
  | emit step _ ih =>
    apply observe_injective
    rw [hk, step]
    simp [layerMap, observe, ih, Option.map]

theorem unfoldTrace_unique (body : S → Layer A X S) (k : S → Model A X)
    (hk : ∀ s, observe (k s) = layerMap k (body s)) : k = unfoldTrace body := by
  funext s
  cases hs : k s with
  | inl r =>
    obtain ⟨w, x⟩ := r
    exact (unfoldTrace_return (returns_of_model body k hk hs)).symm
  | inr seq =>
    have none : ¬ ∃ r : List A × X, Returns body s r.1 r.2 := by
      rintro ⟨⟨w, x⟩, h⟩
      have eq := model_of_returns hk h
      rw [hs] at eq
      contradiction
    rw [unfoldTrace_hang none]
    have eq := output_unique body k hk s
    rw [hs] at eq
    exact congrArg Sum.inr eq

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits

theorem parameter_map {Z : Type u} (f : S ⟶ Z) (o : Layer A X S) :
    ((family A).toParametrizedMonad.parameter X).map f (Part.ofOption o) =
      Part.ofOption (layerMap f o) := by
  cases o with
  | none =>
    change Part.map (fun t : X ⊕ (A × S) =>
      typeCoproducts.map (𝟙 X) ((signature A).map f) t) Part.none = Part.none
    exact Part.map_none _
  | some o => rcases o with x | ⟨a, s⟩ <;> rfl

noncomputable def corecHom (A X : Type u)
    (S : Coalgebra ((family A).toParametrizedMonad.parameter X)) : S ⟶ coalgebra A X where
  f := TypeCat.ofHom (unfoldTrace (Part.equivOption ∘ S.str))
  h := by
    apply ConcreteCategory.hom_ext
    intro s
    let body : S.V → Layer A X S.V := Part.equivOption ∘ S.str
    have e : Part.ofOption (body s) = S.str s := Part.equivOption.symm_apply_apply _
    change ((family A).toParametrizedMonad.parameter X).map
      (TypeCat.ofHom (unfoldTrace body)) (S.str s) =
      Part.ofOption (observe (unfoldTrace body s))
    exact (congrArg (((family A).toParametrizedMonad.parameter X).map
      (TypeCat.ofHom (unfoldTrace body))) e.symm).trans
      ((parameter_map (TypeCat.ofHom (unfoldTrace body)) (body s)).trans
        (congrArg Part.ofOption (unfoldTrace_spec body s).symm))

noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) := by
  refine IsTerminal.ofUniqueHom (corecHom A X) ?_
  intro S k
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro s
  let body : S.V → Layer A X S.V := Part.equivOption ∘ S.str
  apply congrFun (unfoldTrace_unique body k.f ?_) s
  intro t
  have h := ConcreteCategory.congr_hom k.h t
  change ((family A).toParametrizedMonad.parameter X).map k.f (S.str t) =
    Part.ofOption (observe (k.f t)) at h
  have e : Part.ofOption (body t) = S.str t := Part.equivOption.symm_apply_apply _
  apply Part.equivOption.symm.injective
  exact h.symm.trans
    ((congrArg (((family A).toParametrizedMonad.parameter X).map k.f) e.symm).trans
      (parameter_map k.f (body t)))

@[expose] noncomputable def resumptions (A : Type u) :
    FinalResumptions (family A).toParametrizedMonad where
  coalgebra := coalgebra A
  final := terminal A

theorem unit_eq (A X : Type u) (x : X) : (resumptions A).unit X x = Sum.inl ([], x) := by
  apply observe_injective
  apply Part.equivOption.symm.injective
  exact ConcreteCategory.congr_hom ((resumptions A).unit_out X) x

attribute [local instance] seqAction

private theorem bind_emit {Y : Type u} (a : A) (t : Model A X) (f : X → Model A Y) :
    WriterAction.bind (emit a t) f = emit a (WriterAction.bind t f) := by
  rcases t with ⟨w, x⟩ | s
  · change WriterAction.prependOutput (a :: w) (f x) =
      emit a (WriterAction.prependOutput w (f x))
    cases f x with
    | inl p => cases p; rfl
    | inr v =>
      change Sum.inr ((Stream'.Seq.ofList (a :: w)).append v) =
        (Sum.inr (Stream'.Seq.cons a ((Stream'.Seq.ofList w).append v)) : Model A Y)
      rw [Stream'.Seq.ofList_cons, Stream'.Seq.cons_append]
  · rfl

private theorem layer_extend {Y Z : Type u} (f : X → Part (Y ⊕ (A × Z)))
    (p : Part (X ⊕ (A × Z))) :
    (family A).toParametrizedMonad.extend (W := Z) (TypeCat.ofHom f) p =
      p.bind (Sum.elim f (Part.some ∘ Sum.inr)) := by
  have eq := Exception.family_extend typeCoproducts (CategoryTheory.ofTypeMonad Part)
    (A × Z) (TypeCat.ofHom f)
  change ((Exception.family typeCoproducts (CategoryTheory.ofTypeMonad Part)).obj (A × Z)).map
      (TypeCat.ofHom f) ≫ ((Exception.family typeCoproducts (CategoryTheory.ofTypeMonad Part)).obj
       (A × Z)).μ.app Y = _ at eq
  refine (ConcreteCategory.congr_hom eq p).trans ?_
  change joinM ((fun s => Sum.elim f (Part.some ∘ Sum.inr) s) <$> p) = _
  simp [joinM]

theorem extend_eq {Y : Type u} (f : X → Model A Y) (t : Model A X) :
    (resumptions A).extend typeCoproducts (TypeCat.ofHom f) t = WriterAction.bind t f := by
  let bind := TypeCat.ofHom (fun t => WriterAction.bind t f)
  have eq : bind = (resumptions A).extend typeCoproducts (TypeCat.ofHom f) := by
    apply (resumptions A).extend_unique typeCoproducts
    apply ConcreteCategory.hom_ext
    intro t
    change Model A X at t
    let k := Part.ofOption ∘ observe ∘ f
    let extend := (family A).toParametrizedMonad.extend (W := Model A Y) (TypeCat.ofHom k)
    refine Eq.trans ?_ ((layer_extend k (Part.ofOption (layerMap bind (observe t)))).symm.trans
      (congrArg (fun p => extend p) (parameter_map bind (observe t)).symm))
    cases h : observe t with
    | none =>
      have e : t = Sum.inr Stream'.Seq.nil := observe_injective h
      rw [e]
      exact (Part.bind_none _).symm
    | some o =>
      rcases o with x | ⟨a, next⟩
      · have e : t = Sum.inl ([], x) := observe_injective h
        rw [e]
        change Part.ofOption (observe (WriterAction.prependOutput [] (f x))) =
          (Part.some (Sum.inl x)).bind _
        rw [Part.bind_some]
        change Part.ofOption (observe (WriterAction.prependOutput [] (f x))) =
          Part.ofOption (observe (f x))
        rcases f x with ⟨w, y⟩ | seq
        · rfl
        · change Part.ofOption (observe (.inr (Stream'.Seq.nil.append seq))) =
            Part.ofOption (observe (.inr seq) : Layer A Y (Model A Y))
          rw [Stream'.Seq.nil_append]
      · have e : t = emit a next := observe_injective (h.trans (observe_emit a next).symm)
        change Part.ofOption (observe (WriterAction.bind t f)) =
          (Part.some (Sum.inr (a, bind next) : X ⊕ (A × Model A Y))).bind _
        rw [e, bind_emit, observe_emit, Part.bind_some]
        rfl
  exact (congrArg (fun k : Model A X ⟶ Model A Y => k t) eq).symm

end Silmaril.Calco2019.Examples.Printing.Hangs.Proofs
