module

public import Mathlib.Order.WellFounded
public import Silmaril.Semantics.Calco2019.Examples.CountableResumption.Thms
public import Silmaril.Semantics.Calco2019.ExceptionThms
public import Silmaril.Semantics.Calco2019.InductiveResumption.Thms

/-! # Countably nondeterministic signature resumptions on types -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption

open CategoryTheory CategoryTheory.Endofunctor

variable {A : Type u} (B : A → Type u)

/-- The operation functor emits an `a` and receives a reply of type `B a`. -/
def signature : Type u ⥤ Type u where
  obj Z := (a : A) × (B a → Z)
  map f := TypeCat.ofHom fun t => ⟨t.1, f ∘ t.2⟩

/-- The actual parameter family `Choice (X ⊕ H W)`. -/
def family : ParametrizedMonad (Type u) :=
  Exception.parametrized typeCoproducts (CategoryTheory.ofTypeMonad Choice) (signature B)

noncomputable abbrev Inductive (X : Type u) := QPF.Fix (Layer B X)

noncomputable abbrev Coinductive (X : Type u) := QPF.Cofix (Layer B X)

noncomputable def algebra (X : Type u) : Algebra ((family B).parameter X) :=
  ⟨Inductive B X, TypeCat.ofHom QPF.Fix.mk⟩

noncomputable def coalgebra (X : Type u) : Coalgebra ((family B).parameter X) :=
  ⟨Coinductive B X, TypeCat.ofHom QPF.Cofix.dest⟩

/-- Each child is reached by one print followed by a reply. -/
def Child {X Z : Type u} (observe : Z → Layer B X Z) (child parent : Z) : Prop :=
  ∃ (a : A) (k : B a → Z), Sum.inr ⟨a, k⟩ ∈ (observe parent).outcomes ∧
    ∃ reply, k reply = child

/-- The process that repeats the same I/O action after any reply. -/
noncomputable def forever (X : Type u) (a : A) : Coinductive B X :=
  QPF.Cofix.corec (fun _ : PUnit.{u + 1} => (pure (.inr ⟨a, fun _ => PUnit.unit⟩) : Choice (Step B X PUnit.{u + 1}))) PUnit.unit

/-- The one-reply signature gives printing. -/
abbrev PrintingReply (A : Type u) : A → Type u := fun _ => PUnit.{u + 1}

def printingEquiv (A Z : Type u) : ((signature (PrintingReply A)).obj Z) ≃ (A × Z) where
  toFun t := (t.1, t.2 PUnit.unit)
  invFun t := ⟨t.1, fun _ => t.2⟩
  left_inv := by rintro ⟨a, k⟩; rfl
  right_inv := by rintro ⟨a, z⟩; rfl

end Silmaril.Calco2019.Examples.CountableResumption
