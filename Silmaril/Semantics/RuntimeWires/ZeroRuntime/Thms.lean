module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntime.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.ZeroRuntime.Reconstruction

public section

namespace Silmaril.RuntimeWires.Presentation

open CategoryTheory

universe u v

/-- A boundary with zero runtime wires consists exactly of its value wires. -/
theorem values_eraseBoundary {O : Type u} {A : List (Wire O)} (h : runtimeCount A = 0) :
    values (eraseBoundary A) = A :=
  Proofs.ZeroRuntime.restore_boundary h

/-- A single-runtime boundary consists of two value words around one runtime. -/
theorem runtimeCount_one_split {O : Type u} {A : List (Wire O)} (h : runtimeCount A = 1) :
    ∃ L R : List O, A = values L ++ none :: values R :=
  Proofs.ZeroRuntime.split_one h

/-- A tensor in the one-runtime part has one runtime-carrying factor and one pure factor. -/
theorem runtimeCount_one_tensor {O : Type u} (A B : List (Wire O)) (h : runtimeCount (A ++ B) = 1) :
    (runtimeCount A = 1 ∧ runtimeCount B = 0) ∨ (runtimeCount A = 0 ∧ runtimeCount B = 1) :=
  Proofs.ZeroRuntime.tensor_cases A B h

/-- The zero-runtime claim used in the proof of Lemma 3.13. Every runtime
morphism between value-only words admits a representative from the pure category. -/
theorem pureValues_surjective {G : EffectfulPolygraph.{u,v}} {A B : Pure G}
    (f : (pureValues G).obj A ⟶ (pureValues G).obj B) :
    ∃ p : A ⟶ B, (pureValues G).map p = f :=
  Proofs.ZeroRuntime.zero_morphism_rep f

end Silmaril.RuntimeWires.Presentation
