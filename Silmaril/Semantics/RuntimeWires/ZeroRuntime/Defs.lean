module

public import Silmaril.Semantics.RuntimeWires.PureInclusion.Thms
public import Silmaril.Semantics.RuntimeWires.Presentation.Thms

@[expose] public section

/-!
# The zero-runtime part of the presentation

The zero-runtime case of the induction in Lemma 3.13 (p. 9:11) of
Mario Román and Paweł Sobociński, *String Diagrams for Premonoidal Categories*,
arXiv:2305.06075v5.

- PDF: <https://arxiv.org/pdf/2305.06075v5>,
  SHA-256 `8d34da8f010f438e5ff0d0791a3dc338204c55d08ee591a4a18287d193902711`.
- TeX source archive: <https://arxiv.org/src/2305.06075v5>,
  SHA-256 `d1ac1aff3179f351e53daf2905907f7b0ca68ee8d79ffa157c21f8f5755dcfb3`.
-/

namespace Silmaril.RuntimeWires.Presentation

universe u v

/-- Erase runtime wires from a boundary. -/
def eraseBoundary {O : Type u} (A : List (Wire O)) : List O := A.filterMap id

theorem eraseBoundary_append {O : Type u} (A B : List (Wire O)) :
    eraseBoundary (A ++ B) = eraseBoundary A ++ eraseBoundary B :=
  List.filterMap_append

@[simp] theorem eraseBoundary_values {O : Type u} (A : List O) :
    eraseBoundary (values A) = A := by
  induction A with
  | nil => rfl
  | cons a A ih => exact congrArg (a :: ·) ih

@[simp] theorem runtimeCount_values {O : Type u} (A : List O) : runtimeCount (values A) = 0 := by
  induction A with
  | nil => rfl
  | cons a A ih => exact ih

theorem runtimeCount_append {O : Type u} (A B : List (Wire O)) :
    runtimeCount (A ++ B) = runtimeCount A + runtimeCount B := by
  simp only [runtimeCount, List.filter_append, List.length_append]

/-- Every raw diagram on a zero-runtime boundary has a pure representative. -/
def erasePure {G : EffectfulPolygraph.{u,v}} :
    {A B : List (Wire G.Obj)} → Diagram (signature G) A B → runtimeCount A = 0 →
      Diagram G.pure (eraseBoundary A) (eraseBoundary B)
  | _, _, .id A, _ => .id (eraseBoundary A)
  | _, _, .gen (Edge.pure e), _ =>
      Diagram.reindex (eraseBoundary_values _).symm (eraseBoundary_values _).symm (.gen e)
  | _, _, .gen (Edge.effect e), h => by
      change (runtimeCount (values (G.effect.source e))).succ = 0 at h
      exact False.elim (Nat.noConfusion h)
  | _, _, .gen (Edge.moveLeft _), h => False.elim (Nat.noConfusion h)
  | _, _, .gen (Edge.moveRight _), h => False.elim (Nat.noConfusion h)
  | _, _, .comp f g, h =>
      .comp (erasePure f h) (erasePure g ((preservesRuntime f).symm.trans h))
  | _, _, .tensor (A := A) (B := B) (C := C) (D := D) f g, h =>
      let hz := Nat.add_eq_zero_iff.mp ((runtimeCount_append A C).symm.trans h)
      Diagram.reindex (eraseBoundary_append A C).symm (eraseBoundary_append B D).symm
        (.tensor (erasePure f hz.1) (erasePure g hz.2))

end Silmaril.RuntimeWires.Presentation
