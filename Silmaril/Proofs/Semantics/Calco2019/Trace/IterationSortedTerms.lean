module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.SortedTerms.Defs

public section

universe u v w

namespace Silmaril.Calco2019.Proofs.IterationSortedTerms

open CategoryTheory CategoryTheory.Limits IterationTheory

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (Guardedness.greatest P).Fixpoints)

theorem tuple_component {σ : Signature.{w}} {E : Arity}
    (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)
    {n : Nat} (ts : Fin n → Term σ Arity.one E) (i : Fin n) :
    (C.cofan (Fin n)).inj i ≫ (Term.tuple ts).evaluate C F op =
      (C.cofan Arity.one).inj PUnit.unit ≫ (ts i).evaluate C F op := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    let push (i : Fin (n + 1)) : Arity.one.sum (Arity.ofNat n) :=
      Fin.cases (Sum.inl PUnit.unit) (fun j : Fin n => Sum.inr j) i
    change (C.cofan (Fin (n + 1))).inj i ≫ C.reindex push ≫
      (Term.pair (ts 0) (Term.tuple (fun j => ts j.succ))).evaluate C F op = _
    rw [C.reindex_inj_assoc]
    cases i using Fin.cases with
    | zero =>
      simpa only [push, Fin.cases_zero] using
        Term.evaluate_pair_inl C F op (ts 0) (Term.tuple (fun j => ts j.succ)) PUnit.unit
    | succ i =>
      exact (Term.evaluate_pair_inr C F op (ts 0) (Term.tuple (fun j => ts j.succ)) i).trans
        (ih _ i)

theorem generator {S : SortedSignature.{w}} (g : S.Assignment C) (a : S.Symbol) :
    (SortedTerm.generator a).evaluate C F g = g a := by
  apply Cofan.IsColimit.hom_ext (C.colimit (Fin (S.inputs a)))
  intro i
  change (C.cofan (Fin (S.inputs a))).inj i ≫
    (Term.tuple (E := Arity.ofNat (S.outputs a))
      (fun j => Term.generator (σ := S.ranked) ⟨a, j⟩)).evaluate C F (S.components C g) = _
  rw [tuple_component]
  exact Term.evaluate_generator C F (S.components C g) ⟨a, i⟩ PUnit.unit

theorem ranked_valid {S : SortedSignature.{w}} {I E : Arity} (f g : SortedTerm S I E) :
    f.ValidInPointedDomains g ↔ f.ranked.ValidInPointedDomains g.ranked := by
  refine ⟨?_, fun valid D a => valid D (S.components (PointedModel.copowers D) a)⟩
  intro valid D op
  let C := PointedModel.copowers D
  have built := valid D (S.assemble C op)
  have exactComponents : S.components C (S.assemble C op) = op := by
    funext s
    rcases s with ⟨a, i⟩
    exact Cofan.IsColimit.fac (C.colimit (Fin (S.inputs a))) _ i
  change f.ranked.evaluate C PointedModel.conway.toFixpoints
      (S.components C (S.assemble C op)) =
    g.ranked.evaluate C PointedModel.conway.toFixpoints (S.components C (S.assemble C op)) at built
  rw [exactComponents] at built
  exact built

end Silmaril.Calco2019.Proofs.IterationSortedTerms
