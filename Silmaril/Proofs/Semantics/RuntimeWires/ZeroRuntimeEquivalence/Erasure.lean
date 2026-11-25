module

public import Silmaril.Semantics.RuntimeWires.ZeroRuntime.Thms

public section

namespace Silmaril.RuntimeWires.Proofs.ZeroRuntimeEquivalence

open Presentation

universe u v

variable {O : Type u} {S : Signature.{u,v} O}
variable {G : EffectfulPolygraph.{u,v}}

theorem reindex_comp {A B C A' B' C' : List O}
    (p : A = A') (q : B = B') (r : C = C') (f : Diagram S A B) (g : Diagram S B C) :
    Diagram.comp (Diagram.reindex p q f) (Diagram.reindex q r g) =
      Diagram.reindex p r (Diagram.comp f g) := by
  subst p
  subst q
  subst r
  rfl

theorem reindex_tensor {A B C D A' B' C' D' : List O}
    (p : A = A') (q : B = B') (r : C = C') (s : D = D')
    (f : Diagram S A B) (g : Diagram S C D) :
    Diagram.tensor (Diagram.reindex p q f) (Diagram.reindex r s g) =
      Diagram.reindex (congrArg₂ List.append p r) (congrArg₂ List.append q s) (.tensor f g) := by
  subst p
  subst q
  subst r
  subst s
  rfl

theorem reindex_tensor_left {A B C D A' B' : List O}
    (p : A = A') (q : B = B') (f : Diagram S A B) (g : Diagram S C D) :
    Diagram.tensor (Diagram.reindex p q f) g =
      Diagram.reindex (congrArg (· ++ C) p) (congrArg (· ++ D) q) (.tensor f g) :=
  reindex_tensor p q rfl rfl f g

theorem reindex_tensor_right {A B C D C' D' : List O}
    (p : C = C') (q : D = D') (f : Diagram S A B) (g : Diagram S C D) :
    Diagram.tensor f (Diagram.reindex p q g) =
      Diagram.reindex (congrArg (A ++ ·) p) (congrArg (B ++ ·) q) (.tensor f g) :=
  reindex_tensor rfl rfl p q f g

theorem reindex_trans {A B A' B' A'' B'' : List O}
    (p : A = A') (q : B = B') (r : A' = A'') (s : B' = B'') (f : Diagram S A B) :
    Diagram.reindex r s (Diagram.reindex p q f) =
      Diagram.reindex (p.trans r) (q.trans s) f := by
  subst p
  subst q
  subst r
  subst s
  rfl

theorem reindex_id {A B : List O} (p : A = B) :
    Diagram.reindex p p (Diagram.id (S := S) A) = Diagram.id B := by
  subst p
  rfl

theorem reindex_congr {E : Diagram.Equations S} {A B A' B' : List O}
    (p : A = A') (q : B = B') {f g : Diagram S A B} (h : Diagram.Congruence E f g) :
    Diagram.Congruence E (Diagram.reindex p q f) (Diagram.reindex p q g) := by
  subst p
  subst q
  exact h

theorem erase_reindex {A B A' B' : List (Wire G.Obj)} (p : A = A') (q : B = B')
    (f : Diagram (signature G) A B) (h : runtimeCount A' = 0) :
    erasePure (Diagram.reindex p q f) h =
      Diagram.reindex (congrArg eraseBoundary p) (congrArg eraseBoundary q)
        (erasePure f ((congrArg runtimeCount p).trans h)) := by
  subst p
  subst q
  rfl

/-- Erasing a zero-runtime term respects the presentation's entire congruence. -/
theorem erase_congr {A B : List (Wire G.Obj)} {f g : Diagram (signature G) A B}
    (e : Diagram.Congruence (Relations G) f g) (h : runtimeCount A = 0) :
    Diagram.Congruence (fun _ _ => False) (erasePure f h) (erasePure g h) := by
  induction e with
  | equation e =>
    cases e with
    | cancelRight x | cancelLeft x => exact False.elim (Nat.noConfusion h)
    | pureRight e =>
      change (runtimeCount (values (G.pure.source e))).succ = 0 at h
      exact False.elim (Nat.noConfusion h)
    | pureLeft e =>
      have z := h
      change runtimeCount (values (G.pure.source e) ++ [none]) = 0 at z
      rw [runtimeCount_append, runtimeCount_values] at z
      exact False.elim (Nat.noConfusion z)
  | refl => exact .refl _
  | symm _ ih => exact (ih h).symm
  | trans _ _ ih ih' => exact (ih h).trans (ih' h)
  | @comp A B C f f' g g' e e' ih ih' =>
    exact .comp (ih h) (ih' ((preservesRuntime f).symm.trans h))
  | @tensor A B C D f f' g g' e e' ih ih' =>
    have z := Nat.add_eq_zero_iff.mp ((runtimeCount_append A C).symm.trans h)
    exact reindex_congr _ _ (.tensor (ih z.1) (ih' z.2))
  | id_comp f => exact .id_comp (erasePure f h)
  | comp_id f => exact .comp_id (erasePure f h)
  | comp_assoc f g j =>
    have hb := (preservesRuntime f).symm.trans h
    have hc := (preservesRuntime g).symm.trans hb
    exact .comp_assoc (erasePure f h) (erasePure g hb) (erasePure j hc)
  | tensor_id A B =>
    simp only [erasePure]
    simpa only [reindex_id] using
      reindex_congr (eraseBoundary_append A B).symm (eraseBoundary_append A B).symm
        (Diagram.Congruence.tensor_id (E := fun _ _ => False) (eraseBoundary A) (eraseBoundary B))
  | @tensor_comp A B C D F H f g j k =>
    have z := Nat.add_eq_zero_iff.mp ((runtimeCount_append A D).symm.trans h)
    have hb := (preservesRuntime f).symm.trans z.1
    have hf := (preservesRuntime j).symm.trans z.2
    simp only [erasePure, reindex_comp]
    exact reindex_congr _ _
      (.tensor_comp (erasePure f z.1) (erasePure g hb) (erasePure j z.2) (erasePure k hf))
  | tensor_unit_left f =>
    simp only [erase_reindex, erasePure, reindex_trans]
    exact .tensor_unit_left (erasePure f h)
  | tensor_unit_right f =>
    simp only [erase_reindex, erasePure, reindex_trans]
    exact .tensor_unit_right (erasePure f h)
  | @tensor_assoc A B C D F H f g j =>
    have z := Nat.add_eq_zero_iff.mp ((runtimeCount_append A (C ++ F)).symm.trans h)
    have z' := Nat.add_eq_zero_iff.mp ((runtimeCount_append C F).symm.trans z.2)
    let p := (congrArg (eraseBoundary A ++ ·) (eraseBoundary_append C F).symm).trans
      (eraseBoundary_append A (C ++ F)).symm
    let q := (congrArg (eraseBoundary B ++ ·) (eraseBoundary_append D H).symm).trans
      (eraseBoundary_append B (D ++ H)).symm
    simp only [erase_reindex, erasePure, reindex_tensor_left, reindex_tensor_right, reindex_trans]
    simpa only [reindex_trans] using reindex_congr p q
      (Diagram.Congruence.tensor_assoc (E := fun _ _ => False)
        (erasePure f z.1) (erasePure g z'.1) (erasePure j z'.2))

end Silmaril.RuntimeWires.Proofs.ZeroRuntimeEquivalence
