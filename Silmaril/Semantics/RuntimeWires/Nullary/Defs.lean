module

public import Silmaril.Semantics.RuntimeWires.Computations.Defs

@[expose] public section

/-!
# Nullary effectful generator

The one-generator, empty-object signature tests the trivial-centre assertion
preceding Lemma 5.3 in Román and Sobociński's *String Diagrams for Premonoidal Categories*.
-/

namespace Silmaril.RuntimeWires.Nullary

open CategoryTheory Presentation

/-- One effectful generator with empty input and output words. -/
def signatureWithScalar : EffectfulPolygraph.{0,0} where
  Obj := PEmpty
  pure := Signature.empty PEmpty
  effect := ⟨Unit, fun _ => [], fun _ => []⟩

/-- The generator at the single-runtime boundary. -/
def generator : Diagram (signature signatureWithScalar) [none] [none] :=
  Diagram.gen (S := signature signatureWithScalar) (Edge.effect (G := signatureWithScalar) ())

/-- The empty value word. This is the sole object of the computation category. -/
def unitWord : Computations signatureWithScalar := ⟨[]⟩

/-- The nullary effect interpreted as an arrow of the computation category. -/
def effectfulScalar : unitWord ⟶ unitWord :=
  Diagram.Presented.ofTerm generator

end Silmaril.RuntimeWires.Nullary
