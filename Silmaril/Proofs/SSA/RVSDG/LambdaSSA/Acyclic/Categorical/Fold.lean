module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Defs

/-! # Compositionality of the acyclic typed label allocation -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Proofs

open CategoryTheory CategoryTheory.Limits
open LinearChain (Site)

universe u v w h k
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {V : Type v} {C : Type w} [Category.{h} V] [Category.{k} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : Isotope.LetIter.Semantics.Categorical.TypeModel τ V)
  [Isotope.LetIter.Semantics.Categorical.InstructionModel J M Φ]

variable {L R S : List τ} {A B : τ} {T U : C}

theorem blockArrow_rename (b : Block Φ L A) (ρ : ∀ {X}, Site L X → Site R X)
    (arrows : LabelArrows J M R T) :
    blockArrow J M arrows (b.rename ρ) = blockArrow J M (fun X p => arrows X (ρ p)) b := by
  cases b <;> rfl

theorem blockArrow_post (b : Block Φ L A) (arrows : LabelArrows J M L T) (k : T ⟶ U) :
    blockArrow J M arrows b ≫ k = blockArrow J M (fun X p => arrows X p ≫ k) b := by
  cases b <;> simp only [blockArrow, Category.assoc, coprod.desc_comp]

theorem solves_of_blocks (code : Extension Φ L R) (arrows : LabelArrows J M R T)
    (hb : ∀ i, arrows _ (code.local i) = blockArrow J M arrows (code.block i)) :
    Solves J M code arrows := by
  induction code with
  | empty => trivial
  | push prev b ih =>
    refine ⟨?_, ?_⟩
    · exact (hb ⟨0, by simp [Extension.locals]⟩).trans (blockArrow_rename J M b _ _)
    · apply ih
      intro i
      exact (hb i.succ).trans (blockArrow_rename J M (prev.block i) _ _)

private theorem lift_then (first : Extension Φ L R) (next : Extension Φ R S) (p : Site L A) :
    (first.then next).lift p = next.lift (first.lift p) := by
  induction next with
  | empty => rfl
  | push prev b ih => simp only [Extension.then, Extension.lift, ih]

private theorem solves_then (first : Extension Φ L R) (next : Extension Φ R S)
    (arrows : LabelArrows J M S T) :
    Solves J M (first.then next) arrows ↔
      Solves J M next arrows ∧ Solves J M first (fun X p => arrows X (next.lift p)) := by
  induction next with
  | empty => simp [Extension.then, Extension.lift, Solves]
  | push prev b ih =>
    simp only [Extension.then, Extension.lift, Solves, ih, and_assoc]

/-- Every solution of the compiled forward edges agrees at entry with the
structured body followed by the supplied interpretation of its join. -/
theorem compile_fold (b : Body Φ A B) (join : Site L B)
    (arrows : LabelArrows J M (b.compile join).labels T)
    (solve : Solves J M (b.compile join).code arrows) :
    arrows A (b.compile join).entry =
      denote J M b ≫ arrows B ((b.compile join).code.lift join) := by
  induction b generalizing L with
  | instruction op =>
    exact solve.1
  | sequence first next ihFirst ihNext =>
    let t := next.compile join
    let h := first.compile t.entry
    change Solves J M (t.code.then h.code) arrows at solve
    obtain ⟨atHead, atTail⟩ := (solves_then J M t.code h.code arrows).mp solve
    have start := ihFirst t.entry arrows atHead
    have finish := ihNext join (fun X p => arrows X (h.code.lift p)) atTail
    change arrows _ h.entry = (denote J M first ≫ denote J M next) ≫
      arrows _ ((t.code.then h.code).lift join)
    rw [start, finish, lift_then, Category.assoc]
  | choice op left right ihLeft ihRight =>
    let r := right.compile join
    let l := left.compile (r.code.lift join)
    let next := fun X (p : Site l.labels X) => arrows X (shiftSite _ p)
    change Solves J M (.push (r.code.then l.code) (.branch op l.entry (l.code.lift r.entry))) arrows at solve
    obtain ⟨atLeft, atRight⟩ := (solves_then J M r.code l.code next).mp solve.2
    have leftFold := ihLeft (r.code.lift join) next atLeft
    have rightFold := ihRight join (fun X p => next X (l.code.lift p)) atRight
    change arrows _ (headSite _ l.labels) = (LinearChain.Categorical.choice J M op ≫
      coprod.desc (denote J M left) (denote J M right)) ≫
      next _ ((r.code.then l.code).lift join)
    rw [solve.1]
    change LinearChain.Categorical.choice J M op ≫
      coprod.desc (next _ l.entry) (next _ (l.code.lift r.entry)) = _
    rw [leftFold, rightFold, lift_then, Category.assoc, coprod.desc_comp]

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Categorical.Proofs
