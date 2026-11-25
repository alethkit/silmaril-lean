module

public import Silmaril.Semantics.Calco2019.Examples.CountableResumption.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.CountableResumption

/-! # Polynomial presentation of countably nondeterministic I/O layers -/

public section

universe u

namespace Silmaril.Calco2019.Examples.CountableResumption

instance : LawfulMonad (Choice.{u}) := Proofs.choice_lawful

theorem Choice.ext {X : Type u} {p q : Choice X} (h : p.outcomes = q.outcomes) : p = q :=
  Proofs.choice_ext h

theorem Choice.mem_map {X Y : Type u} (f : X → Y) (p : Choice X) (y : Y) :
    y ∈ (f <$> p).outcomes ↔ y ∈ f '' p.outcomes :=
  Proofs.choice_mem_map f p y

open Enumeration

theorem Enumeration.abs_repr {A X Z : Type u} (B : A → Type u) (p : Layer B X Z) :
    abs B (repr B p) = p :=
  Proofs.abs_repr B p

theorem Enumeration.abs_map {A X Z W : Type u} (B : A → Type u) (f : Z → W)
    (p : polynomial B X Z) :
    abs B ((polynomial B X).map f p) = stepMap f <$> (abs B p : Choice (Step B X Z)) :=
  Proofs.abs_map B f p

noncomputable instance {A : Type u} (B : A → Type u) (X : Type u) :
    QPF (Layer B X) where
  map f p := @Functor.map Choice inferInstance _ _ (stepMap f) p
  P := polynomial B X
  abs := abs B
  repr := repr B
  abs_repr := Enumeration.abs_repr B
  abs_map := Enumeration.abs_map B

theorem layer_map {A X Z W : Type u} {B : A → Type u} (f : Z → W) (p : Layer B X Z) :
    f <$> p = (show Choice (Step B X W) from stepMap f <$> (p : Choice (Step B X Z))) := by
  rfl

end Silmaril.Calco2019.Examples.CountableResumption
