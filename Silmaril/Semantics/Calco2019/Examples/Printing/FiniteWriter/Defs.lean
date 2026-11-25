module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Logic.Equiv.Set
public import Silmaril.Semantics.Calco2019.Examples.SetModels.Nonempty.Thms

/-! # The finite-return nondeterministic writer in CALCO 2019, §1.1 -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.FiniteWriter

open SetModels (NonemptyPowerset)

/-- A nonempty set of finite output words paired with return values. -/
abbrev Model (A : Type u) := WriterT (FreeMonoid A) NonemptyPowerset

variable {A X : Type u}

/-- Put the word first and use its list representation. -/
def wordResult : X × FreeMonoid A ≃ List A × X :=
  (Equiv.prodCongr (Equiv.refl X) FreeMonoid.toListEquiv).trans (Equiv.prodComm X (List A))

/-- Identify the writer transformer carrier with the paper's nonempty powerset. -/
def observe : Model A X ≃ NonemptyPowerset (List A × X) :=
  let run : Model A X ≃ NonemptyPowerset (X × FreeMonoid A) :=
    ⟨WriterT.run, WriterT.mk, fun _ => rfl, fun _ => rfl⟩
  run.trans ((Equiv.setCongr wordResult).subtypeEquiv fun _ =>
    ⟨fun h => h.image _, Set.Nonempty.of_image⟩)

/-- The finite word and return pairs of a computation. -/
def outcomes (p : Model A X) : Set (List A × X) := (observe p).1.run

end Silmaril.Calco2019.Examples.Printing.FiniteWriter
