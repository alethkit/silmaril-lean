module

public import Silmaril.Semantics.RuntimeWires.Presentation.Defs

@[expose] public section

namespace Silmaril.RuntimeWires.Proofs

open Presentation

universe u v

private theorem count_values {O : Type u} (A : List O) : runtimeCount (values A) = 0 := by
  induction A with
  | nil => rfl
  | cons => simp [values, runtimeCount, *]

theorem preservesRuntime {G : EffectfulPolygraph.{u,v}} {A B : List (Wire G.Obj)}
    (f : Diagram (signature G) A B) : runtimeCount A = runtimeCount B := by
  induction f with
  | id => rfl
  | gen e =>
    cases e with
    | pure e => simp only [count_values]
    | effect e =>
      change runtimeCount (none :: values (G.effect.source e)) =
        runtimeCount (none :: values (G.effect.target e))
      simp only [runtimeCount, List.filter_cons, Option.isNone_none, ite_true, List.length_cons]
      exact congrArg (· + 1) ((count_values _).trans (count_values _).symm)
    | moveRight => rfl
    | moveLeft => rfl
  | comp _ _ hf hg => exact hf.trans hg
  | tensor _ _ hf hg =>
    simp only [runtimeCount, List.filter_append, List.length_append] at *
    exact congrArg₂ (· + ·) hf hg

theorem homPreservesRuntime {G : EffectfulPolygraph.{u,v}} {A B : List (Wire G.Obj)}
    (f : Hom G A B) : runtimeCount A = runtimeCount B :=
  Quotient.inductionOn f preservesRuntime

end Silmaril.RuntimeWires.Proofs
