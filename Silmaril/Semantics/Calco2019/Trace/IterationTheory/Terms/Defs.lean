module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Interpretation.Thms
public import Mathlib.Basic.Finite.Sum

/-! # Iteration terms on a ranked signature

Finite index types describe the input and output arities. A base map
covers identities, projections in the dual of the theory, and initial maps.
Separated sum is the pairing of two terms after their outputs are injected
into the common target.
-/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory

open CategoryTheory CategoryTheory.Limits

/-- The finite index set of a chosen copower. -/
structure Arity where
  ports : Type
  finite : Finite ports

instance : CoeSort Arity Type := ⟨Arity.ports⟩
instance (A : Arity) : Finite A := A.finite

namespace Arity

/-- The standard index set for (n) inputs or outputs. -/
def ofNat (n : Nat) : Arity := ⟨Fin n, inferInstance⟩

/-- A singleton index set for an operation's sole input in the coproduct theory. -/
def one : Arity := ⟨PUnit, inferInstance⟩

/-- The ports of a coproduct. -/
abbrev sum (A B : Arity) : Arity := ⟨A ⊕ B, inferInstance⟩

end Arity

/-- Equational syntax for the coproduct convention of iteration theories. -/
inductive Term (σ : Signature.{w}) : Arity → Arity → Type (max 1 w)
  | base {I E : Arity} (f : I → E) : Term σ I E
  | generator (a : σ.Symbol) : Term σ Arity.one (Arity.ofNat (σ.arity a))
  | pair {I J E : Arity} : Term σ I E → Term σ J E → Term σ (I.sum J) E
  | comp {I J E : Arity} : Term σ I J → Term σ J E → Term σ I E
  | iterate {I E : Arity} : Term σ I (E.sum I) → Term σ I E

namespace FiniteCopowers

variable {K : Type u} [Category.{v} K] {X : K} (C : FiniteCopowers X)

/-- The arrow from the copower on the disjoint union to the selected
binary coproduct of the two copowers. -/
def split (P : Coproducts K) (I E : Arity) :
    (C.cofan (I.sum E)).pt ⟶ P.sum (C.cofan I).pt (C.cofan E).pt :=
  Cofan.IsColimit.desc (C.colimit (I.sum E))
    (Sum.elim (fun i => (C.cofan I).inj i ≫ P.inl) (fun e => (C.cofan E).inj e ≫ P.inr))

/-- The inverse copower comparison sends the two summands into the copower
on their disjoint union. -/
def join (P : Coproducts K) (I E : Arity) :
    P.sum (C.cofan I).pt (C.cofan E).pt ⟶ (C.cofan (I.sum E)).pt :=
  P.desc (C.reindex Sum.inl) (C.reindex Sum.inr)

end FiniteCopowers

namespace Term

variable {σ : Signature.{w}} {I J E : Arity}

/-- Separated sum is definable from pairing, composition and base maps. -/
def separated (f : Term σ I E) {R : Arity} (g : Term σ J R) :
    Term σ (I.sum J) (E.sum R) :=
  .pair (.comp f (.base Sum.inl)) (.comp g (.base Sum.inr))

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K} (C : FiniteCopowers X)
  (F : (Guardedness.greatest P).Fixpoints) (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)

/-- Evaluate a term in a categorical interpretation of its operations. -/
def evaluate : {I E : Arity} → Term σ I E → ((C.cofan I).pt ⟶ (C.cofan E).pt)
  | _, _, .base f => C.reindex f
  | _, _, .generator a => Cofan.IsColimit.desc (C.colimit Arity.one) (fun _ => op a)
  | _, _, .pair f g => C.split P _ _ ≫ P.desc (evaluate f) (evaluate g)
  | _, _, .comp f g => evaluate f ≫ evaluate g
  | _, _, .iterate f => F.iterate (evaluate f ≫ C.split P _ _) True.intro

end Term

end Silmaril.Calco2019.IterationTheory
