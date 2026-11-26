module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.Syntax.Thms
public import Mathlib.Data.Fin.SuccPred

/-! # Maps of signatures extended with undefined behaviour -/

@[expose] public section
noncomputable section

namespace Silmaril.Isotope.Institution.Refinement.UB

open CategoryTheory Limits
open Silmaril.Logic.Metatheory Silmaril.Logic.Metatheory.TheoryModel

universe u v

/-- Discrete signature extension with a chosen free explicit syntax. -/
noncomputable def adjoin (P : PSig.{u,v,max u v}) : PSig.{u,v,max u v} :=
  ⟨P.Index, signature P.sig, syntaxAlgebra P.sig, syntaxIsInitial P.sig⟩

/-- A nullary target operation at the image of each source sort. -/
abbrev Nullary {J : Type u} (T : TheoryModel.Signature.{u,v} J) (i : J) :=
  {o : T.Op i // T.arity o = 0}

/-- Include the original operations. -/
def inclusion (P : PSig.{u,v,max u v}) : P ⟶ adjoin P where
  sort := id
  op := some
  arg _ := Equiv.refl _
  argSort _ _ := rfl

/-- Extend an operation map by sending each fresh symbol to its specified nullary image. -/
def extend {P Q : PSig.{u,v,max u v}} (f : P ⟶ Q)
    (c : (i : P.Index) → Nullary Q.sig ((PSig.toSig f).sort i)) : adjoin P ⟶ Q where
  sort := (PSig.toSig f).sort
  op := fun {i} o => match o with
    | none => (c i).val
    | some o => (PSig.toSig f).op o
  arg := fun {i} o => match o with
    | none => finCongr (c i).property
    | some o => (PSig.toSig f).arg o
  argSort := fun {i} o => match o with
    | none => fun j => Fin.elim0 (finCongr (c i).property j)
    | some o => (PSig.toSig f).argSort o

variable {P Q : PSig.{u,v,max u v}}

/-- Read a nullary symbol as a closed term in its judgment sort. -/
def constant (P : PSig.{u,v,max u v}) {i : P.Index} (c : Nullary P.sig i) : P.syn.Carrier i :=
  P.syn.op c.val (fun j => Fin.elim0 (finCongr c.property j))

/-- Relabel the old operations and retain the fresh symbol at the translated sort. -/
def map (f : P ⟶ Q) : adjoin P ⟶ adjoin Q :=
  extend (f ≫ inclusion Q) (fun _ => ⟨none, rfl⟩)

/-- Fold both layers of fresh symbols into the single fresh symbol. -/
def collapse (P : PSig.{u,v,max u v}) : adjoin (adjoin P) ⟶ adjoin P :=
  extend (𝟙 (adjoin P)) (fun _ => ⟨none, rfl⟩)

end Silmaril.Isotope.Institution.Refinement.UB
