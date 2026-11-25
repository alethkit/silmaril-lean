module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.ZeroRuntimeEquivalence.Erasure

public section

namespace Silmaril.RuntimeWires.Proofs.ZeroRuntimeEquivalence

open CategoryTheory
open Presentation
open scoped MonoidalCategory

universe u v

variable {G : EffectfulPolygraph.{u,v}}

/-- Interpret a pure term as raw syntax on value-only runtime boundaries. -/
private def liftTerm : {A B : List G.Obj} → Diagram G.pure A B →
    Diagram (signature G) (values A) (values B)
  | _, _, .id A => .id (values A)
  | _, _, .gen e => pureDiagram e
  | _, _, .comp f g => .comp (liftTerm f) (liftTerm g)
  | _, _, .tensor (A := A) (B := B) (C := C) (D := D) f g =>
    Diagram.reindex (List.map_append (f := some) (l₁ := A) (l₂ := C)).symm
      (List.map_append (f := some) (l₁ := B) (l₂ := D)).symm (.tensor (liftTerm f) (liftTerm g))

private theorem ofTerm_reindex {A B A' B' : List (Wire G.Obj)} (p : A = A') (q : B = B')
    (f : Diagram (signature G) A B) :
    Diagram.Presented.ofTerm (A := (⟨A'⟩ : Runtime G)) (B := ⟨B'⟩) (Diagram.reindex p q f) =
      eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) p).symm ≫
        Diagram.Presented.ofTerm f ≫
        eqToHom (congrArg (Diagram.Presented.mk (S := signature G) (E := Relations G)) q) := by
  subst p
  subst q
  simp [Diagram.reindex]

private theorem pureTerm_liftTerm {A B : List G.Obj} (f : Diagram G.pure A B) :
    pureTerm f = Diagram.Presented.ofTerm (A := valueWord A) (B := valueWord B) (liftTerm f) := by
  induction f with
  | id | gen => rfl
  | comp f g hf hg =>
    change pureTerm f ≫ pureTerm g = Diagram.Presented.ofTerm (.comp (liftTerm f) (liftTerm g))
    rw [hf, hg]
    rfl
  | @tensor A B C D f g hf hg =>
    simp only [pureTerm, liftTerm, hf, hg]
    exact (ofTerm_reindex (List.map_append (f := some) (l₁ := A) (l₂ := C)).symm
      (List.map_append (f := some) (l₁ := B) (l₂ := D)).symm
      (.tensor (liftTerm f) (liftTerm g))).symm

private theorem erase_liftTerm {A B : List G.Obj} (f : Diagram G.pure A B) :
    erasePure (liftTerm f) (runtimeCount_values A) =
      Diagram.reindex (eraseBoundary_values A).symm (eraseBoundary_values B).symm f := by
  induction f with
  | id => exact (reindex_id _).symm
  | gen => rfl
  | comp f g hf hg =>
    simp only [liftTerm, erasePure, hf, hg, reindex_comp]
  | tensor f g hf hg =>
    simp only [liftTerm, erase_reindex, erasePure, hf, hg, reindex_tensor, reindex_trans]

theorem erase_section {A B : Pure G} (f : A ⟶ B) :
    eraseValueMorphism ((pureValues G).map f) = f := by
  refine Quotient.inductionOn f fun t => ?_
  change eraseValueMorphism (pureTerm t) = Diagram.Presented.ofTerm t
  rw [pureTerm_liftTerm t]
  change Diagram.Presented.ofTerm (Diagram.reindex
    (eraseBoundary_values A.word) (eraseBoundary_values B.word)
    (erasePure (liftTerm t) (runtimeCount_values A.word))) = Diagram.Presented.ofTerm t
  rw [erase_liftTerm t, reindex_trans]
  rfl

end Silmaril.RuntimeWires.Proofs.ZeroRuntimeEquivalence
