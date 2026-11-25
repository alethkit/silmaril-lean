module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Completeness.Thms

/-! # Iteration terms with arbitrary finite-arity generators

The reduction to ranked signatures replaces each (n)-to-(p) generator
by its (n) components of arity (p).
-/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory CategoryTheory.Limits

namespace Term

variable {σ : Signature.{w}} {E : Arity}

/-- The tuple of a finite family of single-input terms. -/
def tuple : {n : Nat} → (Fin n → Term σ Arity.one E) → Term σ (Arity.ofNat n) E
  | 0, _ => .base Fin.elim0
  | n + 1, f =>
    .comp (.base (Fin.cases (Sum.inl PUnit.unit) (fun j : Fin n => Sum.inr j)))
      (.pair (f 0) (tuple (fun j => f j.succ)))

end Term

/-- Variables with arbitrary finite source and target arities. -/
structure SortedSignature where
  Symbol : Type w
  inputs : Symbol → Nat
  outputs : Symbol → Nat

namespace SortedSignature

/-- Turn each input component into a ranked symbol at the same output arity. -/
abbrev ranked (S : SortedSignature.{w}) : Signature.{w} where
  Symbol := (a : S.Symbol) × Fin (S.inputs a)
  arity s := S.outputs s.1

variable (S : SortedSignature.{w}) {K : Type u} [Category.{v} K] {X : K} (C : FiniteCopowers X)

/-- Interpret a sorted generator as an arrow between its two copowers. -/
abbrev Assignment :=
  ∀ a : S.Symbol, (C.cofan (Fin (S.inputs a))).pt ⟶ (C.cofan (Fin (S.outputs a))).pt

/-- Restrict a sorted assignment to each ranked input component. -/
def components (g : S.Assignment C) (s : S.ranked.Symbol) :
    X ⟶ (C.cofan (Fin (S.ranked.arity s))).pt :=
  (C.cofan (Fin (S.inputs s.1))).inj s.2 ≫ g s.1

/-- Assemble ranked components into the corresponding sorted assignment. -/
def assemble (g : ∀ s : S.ranked.Symbol, X ⟶ (C.cofan (Fin (S.ranked.arity s))).pt) :
    S.Assignment C :=
  fun a => Cofan.IsColimit.desc (C.colimit (Fin (S.inputs a))) (fun i => g ⟨a, i⟩)

end SortedSignature

/-- Iteration terms with general many-sorted variables. -/
inductive SortedTerm (S : SortedSignature.{w}) : Arity → Arity → Type (max 1 w)
  | base {I E : Arity} (f : I → E) : SortedTerm S I E
  | generator (a : S.Symbol) : SortedTerm S (Arity.ofNat (S.inputs a)) (Arity.ofNat (S.outputs a))
  | pair {I J E : Arity} : SortedTerm S I E → SortedTerm S J E → SortedTerm S (I.sum J) E
  | comp {I J E : Arity} : SortedTerm S I J → SortedTerm S J E → SortedTerm S I E
  | iterate {I E : Arity} : SortedTerm S I (E.sum I) → SortedTerm S I E

namespace SortedTerm

variable {S : SortedSignature.{w}} {I E : Arity}

/-- Separated sum pairs the terms after injecting their respective outputs. -/
def separated {J R : Arity} (f : SortedTerm S I E) (g : SortedTerm S J R) :
    SortedTerm S (I.sum J) (E.sum R) :=
  .pair (.comp f (.base Sum.inl)) (.comp g (.base Sum.inr))

/-- Replace generators by the tuple of their ranked input components. -/
def ranked : {I E : Arity} → SortedTerm S I E → Term S.ranked I E
  | _, _, .base f => .base f
  | _, _, .generator a => Term.tuple (fun i => Term.generator (σ := S.ranked) ⟨a, i⟩)
  | _, _, .pair f g => .pair (ranked f) (ranked g)
  | _, _, .comp f g => .comp (ranked f) (ranked g)
  | _, _, .iterate f => .iterate (ranked f)

/-- Evaluate a sorted term by interpreting its ranked input components. -/
def evaluate {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
    (C : FiniteCopowers X) (F : (Guardedness.greatest P).Fixpoints)
    (g : S.Assignment C) (f : SortedTerm S I E) :
    (C.cofan I).pt ⟶ (C.cofan E).pt :=
  f.ranked.evaluate C F (S.components C g)

/-- An equation under every assignment of its many-sorted generators to
continuous maps between powers of a pointed domain. -/
def ValidInPointedDomains (f g : SortedTerm S I E) : Prop :=
  ∀ (D : PointedModel.Object.{w}) (a : S.Assignment (PointedModel.copowers D)),
    f.evaluate (PointedModel.copowers D) PointedModel.conway.toFixpoints a =
      g.evaluate (PointedModel.copowers D) PointedModel.conway.toFixpoints a

end SortedTerm

end Silmaril.Calco2019.IterationTheory
