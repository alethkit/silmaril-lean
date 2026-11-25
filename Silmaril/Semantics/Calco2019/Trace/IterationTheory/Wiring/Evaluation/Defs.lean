module

public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Wiring.Defs
public import Silmaril.Semantics.Calco2019.Trace.IterationTheory.Terms.Thms
public import Silmaril.Semantics.Calco2019.Trace.Vanishing.Thms

/-! # Categorical evaluation of finite equation graphs -/

@[expose] public section

universe u v w

namespace Silmaril.Calco2019.IterationTheory.Wiring

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {X : K}
  (C : FiniteCopowers X) (F : (Guardedness.greatest P).Fixpoints)
  {σ : Signature.{w}} {I E S : Arity}
  (op : ∀ a : σ.Symbol, X ⟶ (C.cofan (Fin (σ.arity a))).pt)

/-- A graph exits through the corresponding output port. An explicit bottom
is interpreted by the chosen fixpoint of a loop with no exit. -/
def interpretation : Interpretation C σ E (C.cofan E).pt where
  op := op
  exit := (C.cofan E).inj
  bottom := F.iterate P.inr True.intro

/-- The arrow for one row. A jump selects its new state with no operation. -/
def branch : Instruction σ E S → (X ⟶ P.sum (C.cofan E).pt (C.cofan S).pt)
  | .head h => (interpretation C F op).branch h
  | .jump s => (C.cofan S).inj s ≫ P.inr

/-- Assemble the rows as a simultaneous system. -/
def body (g : Wiring σ I E) :
    (C.cofan g.states).pt ⟶ P.sum (C.cofan E).pt (C.cofan g.states).pt :=
  Cofan.IsColimit.desc (C.colimit g.states) (fun s => branch C F op (g.row s))

/-- Solve the graph and select the components named by its entries. -/
def evaluate (g : Wiring σ I E) : (C.cofan I).pt ⟶ (C.cofan E).pt :=
  C.reindex g.entry ≫ F.iterate (g.body C F op) True.intro

end Silmaril.Calco2019.IterationTheory.Wiring
