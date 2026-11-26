module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseAndUnaryReturns.Denotation.Preservation.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Thms

/-! # The full structural witness in a weak interaction-tree model -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservationExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Elgot.ITree
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Semantics.Interaction Semantics.Interaction.Typed
open Paper.WithCaseAndUnaryReturns (Step denoteFunctor denoteFunctor_preserves denoteFunctor_map_primitive)
open Paper.Extension.Singleton (ofType whiskerLeftFunctor)
open Paper.Extension.Singleton.Generation

private abbrev Atom := PEmpty.{2}

local instance : AtomValues Atom where
  carrier := PEmpty.elim

private inductive Op where
  | poll

private inductive Request : Type → Type where
  | poll : Request Bool

local instance : HasTy Op (Ty Atom) where
  src _ := .unit
  trg _ := .unit

local instance : HasEff Op Bool where
  eff _ := true

attribute [local instance] typeModel

local notation "Atoms" => AtomValues.carrier (κ := Atom)
local notation "TM" => ModelTree Request

local instance : InstructionModel Op (Ty Atom) Bool TM where
  denote _ _ := vis .poll (fun _ => pure PUnit.unit)
  denotePure f h := by cases h
  denote_pure f h := by cases h

private def raw : Primitive Request Op (Sigma Atoms) :=
  fun _ _ => vis .poll (fun _ => pure .unit)

set_option backward.isDefEq.respectTransparency false in
private theorem compatible :
    Compatible (κ' := Atom) ⟨fun f x => InstructionModel.denote
      (τ := Ty Atom) (ε := Bool) (m := TM) f x⟩ raw := by
  intro f x
  change raw f .unit = ((vis .poll (fun _ => pure PUnit.unit) : TM (Ty.denote Atoms .unit)) >>=
    fun y => pure (encodeValue Atoms .unit y))
  unfold raw
  rw [vis_bind]
  congr 1
  funext b
  change (pure .unit : TM (Value (Sigma Atoms))) =
    ((pure PUnit.unit : TM PUnit.{2}) >>= fun y : PUnit.{2} => pure (encodeValue Atoms .unit y))
  rw [pure_bind (m := TM)]
  rfl

attribute [local instance] categoricalInstructions

local notation "J" => typeJ (m := TM)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "shared" => (fun _ _ => Exists.intro rfl rfl)
local notation "Seed" => Step (τ := Ty Atom) (Φ := Op) false
local notation "F" => denoteFunctor (Φ := Op) false J M shared
local notation "coords" => Coordinates.ofModel J M
set_option quotPrecheck false in
local notation "objIso" => (fun A : Ty Atom => Iso.refl ((J).obj ((M).obj A)))

local instance : Semantics.Categorical.RegionTypingCoherent (Φ := Op) J M :=
  regionTypingCoherent raw compatible

private abbrev U : Ty Atom := .unit
private abbrev Capture : Ty Atom := .coprod U U

example : Preserves Seed F objIso coords :=
  denoteFunctor_preserves false J M shared

example :
    mapInCoordinates Seed F objIso
      ((whiskerLeftFunctor Seed (ofType Seed Capture)).map (primitive Seed Op.poll)) =
      ((coords).tensorIso Capture U).hom ≫
        ((J).obj ((M).obj Capture) ◁ mapInCoordinates Seed F objIso (primitive Seed Op.poll)) ≫
        ((coords).tensorIso Capture U).inv :=
  (denoteFunctor_preserves (Φ := Op) false J M shared).left Capture (primitive Seed Op.poll)

set_option backward.isDefEq.respectTransparency false in
example :
    out (((F).map (primitive Seed Op.poll)).of PUnit.unit) =
      Part.some (.vis Request.poll (fun _ => pure PUnit.unit)) := by
  have h := denoteFunctor_map_primitive false J M shared Op.poll
  change 𝟙 _ ≫ (F).map (primitive Seed Op.poll) ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, Category.id_comp] at h
  rw [h]
  exact out_vis Request.poll _

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ReturnDenotationPreservationExample
