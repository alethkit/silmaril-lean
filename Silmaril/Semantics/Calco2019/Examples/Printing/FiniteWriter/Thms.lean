module

public import Silmaril.Semantics.Calco2019.Examples.Printing.FiniteWriter.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingFiniteWriter

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.FiniteWriter

variable {A X Y : Type u}

/-- The writer transformer inherits the monad laws from the nonempty powerset. -/
theorem lawful (A : Type u) : LawfulMonad (Model A) := inferInstance

theorem outcomes_nonempty (p : Model A X) : (outcomes p).Nonempty := (observe p).2

@[simp] theorem outcomes_pure (x : X) : outcomes (pure x : Model A X) = {([], x)} :=
  Proofs.outcomes_pure x

/-- Sequencing takes every continuation outcome and concatenates outputs in execution order. -/
theorem mem_outcomes_bind (p : Model A X) (k : X → Model A Y) (word : List A) (y : Y) :
    (word, y) ∈ outcomes (p >>= k) ↔
      ∃ prefixWord x suffixWord,
        (prefixWord, x) ∈ outcomes p ∧ (suffixWord, y) ∈ outcomes (k x) ∧
          prefixWord ++ suffixWord = word :=
  Proofs.mem_outcomes_bind p k word y

end Silmaril.Calco2019.Examples.Printing.FiniteWriter
