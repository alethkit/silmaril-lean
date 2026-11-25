module

public import Silmaril.Semantics.Calco2019.Examples.Printing.WordResumptions.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingWordResumptions

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.WordResumptions

open CategoryTheory CategoryTheory.Limits

/-- The finite writer's constructor is initial for the one-letter printing layer. -/
noncomputable def initial (A X : Type u) : IsInitial (algebra A X) :=
  Proofs.initial A X

/-- The productive writer's observer is final for the one-letter printing layer. -/
noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) :=
  Proofs.terminal A X

@[expose] noncomputable def initialResumptions (A : Type u) :
    InitialResumptions (family A).toParametrizedMonad where
  algebra := algebra A
  initial := initial A

@[expose] noncomputable def finalResumptions (A : Type u) :
    FinalResumptions (family A).toParametrizedMonad where
  coalgebra := coalgebra A
  final := terminal A

theorem inductive_obj (A X : Type u) :
    (initialResumptions A).obj X = (List A × X) := rfl

theorem coinductive_obj (A X : Type u) :
    (finalResumptions A).obj X = Productive A X := rfl

end Silmaril.Calco2019.Examples.Printing.WordResumptions
