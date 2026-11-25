module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Hangs.Thms
public import Silmaril.Semantics.Calco2019.InductiveResumption.Thms

/-! # Deterministic printing as the initial and final word constructions in §1.2 -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.WordResumptions

open CategoryTheory CategoryTheory.Endofunctor

variable {A X Z : Type u}

noncomputable abbrev family (A : Type u) :=
  Exception.parametrizedElgot (guardedIdentity typeCoproducts) (Hangs.signature A)

def roll : X ⊕ (A × (List A × X)) → List A × X
  | .inl x => ([], x)
  | .inr (a, (w, x)) => (a :: w, x)

def algebra (A X : Type u) : Algebra ((family A).toParametrizedMonad.parameter X) :=
  ⟨List A × X, TypeCat.ofHom roll⟩

def fold (body : X ⊕ (A × Z) → Z) (t : List A × X) : Z :=
  t.1.foldr (fun a v => body (.inr (a, v))) (body (.inl t.2))

/-- A successful finite word or an infinite stream of output. -/
abbrev Productive (A X : Type u) := (List A × X) ⊕ (ℕ → A)

def observe : Productive A X → X ⊕ (A × Productive A X)
  | .inl ([], x) => .inl x
  | .inl (a :: w, x) => .inr (a, .inl (w, x))
  | .inr s => .inr (s 0, .inr (fun i => s (i + 1)))

def coalgebra (A X : Type u) : Coalgebra ((family A).toParametrizedMonad.parameter X) :=
  ⟨Productive A X, TypeCat.ofHom observe⟩

def toHang : Productive A X → Hangs.Model A X :=
  Sum.map id Stream'.Seq.ofStream

def strip {S : Type u} (f : S → X ⊕ (A × S)) (s : S) : Option (A × S) :=
  Sum.elim (fun _ => none) some (f s)

end Silmaril.Calco2019.Examples.Printing.WordResumptions
