module

public import Silmaril.Semantics.Calco2019.Examples.CountableResumption.Coalgebras.Defs

public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption.Proofs

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits

variable {A : Type u} (B : A → Type u)

theorem parameter_map {X Z W : Type u} (f : Z ⟶ W) (p : Layer B X Z) :
    ((family B).parameter X).map f p = f <$> p := by
  change (fun t : Step B X Z => typeCoproducts.map (𝟙 X) ((signature B).map f) t) <$> p = _
  rw [layer_map]
  congr 1
  funext t
  cases t <;> rfl

noncomputable def foldHom (X : Type u) (S : Algebra ((family B).parameter X)) :
    algebra B X ⟶ S where
  f := TypeCat.ofHom (QPF.Fix.rec (F := Layer B X) S.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro p
    let fold := QPF.Fix.rec (F := Layer B X) S.str
    change S.str (((family B).parameter X).map (TypeCat.ofHom fold) p) = fold (QPF.Fix.mk p)
    exact (congrArg (fun t => S.str t) (parameter_map B (TypeCat.ofHom fold) p)).trans
      (QPF.Fix.rec_eq (F := Layer B X) S.str p).symm

noncomputable def initial (X : Type u) : IsInitial (algebra B X) := by
  refine IsInitial.ofUniqueHom (foldHom B X) ?_
  intro S k
  apply Algebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro t
  apply congrFun (QPF.Fix.rec_unique (F := Layer B X) S.str k.f ?_).symm t
  intro p
  have eq := (ConcreteCategory.congr_hom k.h p).symm
  change k.f (QPF.Fix.mk p) = S.str (((family B).parameter X).map k.f p) at eq
  exact eq.trans (congrArg (fun r => S.str r) (parameter_map B k.f p))

theorem corec_unique {X S : Type u} (body : S → Layer B X S) (k : S → Coinductive B X)
    (hk : ∀ s, QPF.Cofix.dest (k s) = k <$> body s) :
    k = QPF.Cofix.corec body := by
  funext s
  refine QPF.Cofix.bisim' (fun _ => True) k (QPF.Cofix.corec body) ?_ s trivial
  intro t _
  let p := QPF.repr (body t)
  have eq : QPF.abs p = body t := QPF.abs_repr _
  refine ⟨p.1, k ∘ p.2, QPF.Cofix.corec body ∘ p.2, ?_, ?_, fun i => ⟨p.2 i, trivial, rfl, rfl⟩⟩
  · rw [hk, ← eq, ← QPF.abs_map]
    rfl
  · rw [QPF.Cofix.dest_corec, ← eq, ← QPF.abs_map]
    rfl

noncomputable def unfoldHom (X : Type u) (S : Coalgebra ((family B).parameter X)) :
    S ⟶ coalgebra B X where
  f := TypeCat.ofHom (QPF.Cofix.corec (F := Layer B X) S.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro s
    change ((family B).parameter X).map (TypeCat.ofHom (QPF.Cofix.corec (F := Layer B X) S.str)) (S.str s) =
      QPF.Cofix.dest (QPF.Cofix.corec (F := Layer B X) S.str s)
    exact (parameter_map B _ (S.str s)).trans (QPF.Cofix.dest_corec (F := Layer B X) S.str s).symm

noncomputable def terminal (X : Type u) : IsTerminal (coalgebra B X) := by
  refine IsTerminal.ofUniqueHom (unfoldHom B X) ?_
  intro S k
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro s
  apply congrFun (corec_unique B S.str k.f ?_) s
  intro t
  have eq := ConcreteCategory.congr_hom k.h t
  change ((family B).parameter X).map k.f (S.str t) = QPF.Cofix.dest (k.f t) at eq
  exact eq.symm.trans (parameter_map B k.f (S.str t))

private theorem pack_all {X Z : Type u} (P : Z → Prop) (tag : X ⊕ A)
    (next : Enumeration.slots B tag → Z) (hp : ∀ b, P (next b)) (a : A) (k : B a → Z)
    (h : Enumeration.pack B tag next = Sum.inr ⟨a, k⟩) (b : B a) : P (k b) := by
  cases tag with
  | inl x => contradiction
  | inr a' =>
    have eq : (⟨a', next⟩ : (a : A) × (B a → Z)) = ⟨a, k⟩ := Sum.inr.inj h
    cases eq
    exact hp b

private theorem all_pack {X Z : Type u} (p : Layer B X Z) (P : Z → Prop)
    (h : ∀ (a : A) (k : B a → Z), Sum.inr ⟨a, k⟩ ∈ p.outcomes → ∀ b, P (k b))
    (tag : X ⊕ A) (next : Enumeration.slots B tag → Z)
    (hm : Enumeration.pack B tag next ∈ p.outcomes) (b : Enumeration.slots B tag) :
    P (next b) := by
  cases tag with
  | inl x => exact PEmpty.elim b
  | inr a => exact h a next hm b

theorem liftp_iff {X Z : Type u} (p : Layer B X Z) (P : Z → Prop) :
    Functor.Liftp P p ↔
      ∀ (a : A) (k : B a → Z), Sum.inr ⟨a, k⟩ ∈ p.outcomes → ∀ b, P (k b) := by
  rw [QPF.liftp_iff]
  constructor
  · rintro ⟨shape, next, rfl, hp⟩ a k hm b
    change Sum.inr ⟨a, k⟩ ∈
      Set.range (fun i => Enumeration.pack B (shape i) fun r => next ⟨i, r⟩) at hm
    obtain ⟨i, hi⟩ := hm
    exact pack_all B P (shape i) (fun r => next ⟨i, r⟩) (fun r => hp ⟨i, r⟩) a k hi b
  · intro h
    let p' := QPF.repr p
    refine ⟨p'.1, p'.2, (QPF.abs_repr p).symm, ?_⟩
    rintro ⟨i, b⟩
    have hm : Enumeration.pack B (p'.1 i) (fun r => p'.2 ⟨i, r⟩) ∈ p.outcomes :=
      (QPF.abs_repr p) ▸ (Set.mem_range_self i :
        Enumeration.pack B (p'.1 i) (fun r => p'.2 ⟨i, r⟩) ∈ (QPF.abs p').outcomes)
    exact all_pack B p P h (p'.1 i) (fun r => p'.2 ⟨i, r⟩) hm b

theorem inductive_wellFounded (X : Type u) :
    WellFounded (Child B (X := X) (QPF.Fix.dest : Inductive B X → _)) := by
  refine ⟨QPF.Fix.ind _ (fun row h => ?_)⟩
  apply Acc.intro
  rw [liftp_iff] at h
  rintro child ⟨a, k, hk, b, rfl⟩
  change Sum.inr ⟨a, k⟩ ∈ (QPF.Fix.dest (QPF.Fix.mk row)).outcomes at hk
  rw [QPF.Fix.dest_mk] at hk
  exact h a k hk b

theorem forever_observe (X : Type u) (a : A) :
    QPF.Cofix.dest (forever B X a) = (pure (.inr ⟨a, fun _ => forever B X a⟩) : Choice (Step B X (Coinductive B X))) := by
  rw [forever, QPF.Cofix.dest_corec, layer_map]
  exact map_pure _ _

theorem bisim_iff {X : Type u} {p q : Coinductive B X} :
    p = q ↔ ∃ R : Coinductive B X → Coinductive B X → Prop, R p q ∧
      ∀ x y, R x y → Functor.Liftr R (QPF.Cofix.dest x) (QPF.Cofix.dest y) := by
  constructor
  · rintro rfl
    refine ⟨Eq, rfl, fun x y h => ?_⟩
    subst y
    let p' := QPF.repr (QPF.Cofix.dest x)
    exact (QPF.liftr_iff _ _ _).2
      ⟨p'.1, p'.2, p'.2, (QPF.abs_repr _).symm, (QPF.abs_repr _).symm, fun _ => rfl⟩
  · intro ⟨R, h, bisim⟩
    exact QPF.Cofix.bisim R bisim _ _ h

end Silmaril.Calco2019.Examples.CountableResumption.Proofs
