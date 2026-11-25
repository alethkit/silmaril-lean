module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntime.Defs
public import Silmaril.Proofs.Semantics.RuntimeWires.PureInclusion.Interpretation

public section

namespace Silmaril.RuntimeWires.Proofs.ZeroRuntime

open CategoryTheory
open Presentation
open scoped MonoidalCategory SameArrow

universe u v

variable {G : EffectfulPolygraph.{u,v}}

theorem restore_boundary {O : Type u} {A : List (Wire O)}
    (h : runtimeCount A = 0) : values (eraseBoundary A) = A := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    cases a with
    | none =>
      change (runtimeCount A).succ = 0 at h
      exact False.elim (Nat.noConfusion h)
    | some a =>
      exact congrArg (some a :: ·) (ih h)

theorem split_one {O : Type u} {A : List (Wire O)} (h : runtimeCount A = 1) :
    ∃ L R : List O, A = values L ++ none :: values R := by
  induction A with
  | nil => exact False.elim (Nat.noConfusion h)
  | cons a A ih =>
    cases a with
    | none =>
      change (runtimeCount A).succ = 1 at h
      exact ⟨[], eraseBoundary A, congrArg (none :: ·) (restore_boundary (Nat.succ.inj h)).symm⟩
    | some a =>
      obtain ⟨L, R, e⟩ := ih h
      exact ⟨a :: L, R, congrArg (some a :: ·) e⟩

theorem tensor_cases {O : Type u} (A B : List (Wire O)) (h : runtimeCount (A ++ B) = 1) :
    (runtimeCount A = 1 ∧ runtimeCount B = 0) ∨ (runtimeCount A = 0 ∧ runtimeCount B = 1) := by
  rw [runtimeCount_append] at h
  omega

private theorem interpret_reindex {A B C D : List G.Obj} (p : A = C) (q : B = D)
    (f : Diagram G.pure A B) : pureTerm (Diagram.reindex p q f) ≈ₐ pureTerm f := by
  subst p
  subst q
  exact SameArrow.refl _

theorem restore_term {A B : List (Wire G.Obj)} (f : Diagram (signature G) A B)
    (h : runtimeCount A = 0) :
    pureTerm (erasePure f h) ≈ₐ
      (Diagram.Presented.ofTerm (A := (⟨A⟩ : Runtime G)) (B := ⟨B⟩) f) := by
  induction f with
  | id A =>
    exact SameArrow.id (congrArg Diagram.Presented.mk (restore_boundary h))
  | gen e =>
    cases e with
    | pure e =>
      exact interpret_reindex (eraseBoundary_values _).symm (eraseBoundary_values _).symm (.gen e)
    | effect e =>
      change (runtimeCount (values (G.effect.source e))).succ = 0 at h
      exact False.elim (Nat.noConfusion h)
    | moveRight _ | moveLeft _ => exact False.elim (Nat.noConfusion h)
  | comp f g hf hg =>
    exact (hf h).comp (hg ((preservesRuntime f).symm.trans h))
  | @tensor A B C D f g hf hg =>
    have hz := Nat.add_eq_zero_iff.mp ((runtimeCount_append A C).symm.trans h)
    exact (interpret_reindex (eraseBoundary_append A C).symm (eraseBoundary_append B D).symm
      (.tensor (erasePure f hz.1) (erasePure g hz.2))).trans
      ((PureInclusion.tensor_term (erasePure f hz.1) (erasePure g hz.2)).trans
        ((hf hz.1).tensor (hg hz.2)))

theorem zero_morphism_rep {A B : Pure G}
    (f : (pureValues G).obj A ⟶ (pureValues G).obj B) :
    ∃ p : A ⟶ B, (pureValues G).map p = f := by
  change valueWord A.word ⟶ valueWord B.word at f
  refine Quotient.inductionOn f fun term => ?_
  have h := runtimeCount_values A.word
  let pure := Diagram.reindex (eraseBoundary_values A.word) (eraseBoundary_values B.word)
    (erasePure term h)
  refine ⟨Diagram.Presented.ofTerm pure, ?_⟩
  rw [pureValues_map_term]
  exact ((interpret_reindex _ _ _).trans (restore_term term h)).eq

end Silmaril.RuntimeWires.Proofs.ZeroRuntime
