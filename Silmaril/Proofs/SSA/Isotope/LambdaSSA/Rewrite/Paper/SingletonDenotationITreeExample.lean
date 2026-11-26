module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Denotation.Functor.ITree.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms

/-! # Visible composition of arbitrary guarded singleton arrows -/

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationITreeExample

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Interaction Semantics.Interaction.Typed Semantics.Categorical
open Region.Paper.TypeCategory Region.Paper.RetainedLet
open Silmaril.Elgot.ITree
open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

private inductive Op where
  | read | write

private abbrev Atom := ULift.{1} Unit

local instance : AtomValues Atom where
  carrier _ := ULift.{1} Nat

attribute [local instance] typeModel

private abbrev A : Ty Atom := .base ⟨()⟩

local instance : HasTy Op (Ty Atom) where
  src _ := A
  trg _ := A

local instance : HasEff Op Bool where
  eff _ := true

private inductive Event : Type → Type where
  | call (op : Op) (arg : Nat) : Event Nat

local notation "TM" => ModelTree Event
local notation "K" => typeJ (m := TM)
local notation "T" => ofMonadicTypeModel (τ := Ty Atom)
local notation "Atoms" => AtomValues.carrier (κ := Atom)

set_option backward.isDefEq.respectTransparency false

local instance : InstructionModel Op (Ty Atom) Bool TM where
  denote f x := vis (.call f x.down) (fun n => pure ⟨n⟩)
  denotePure f h := by cases h
  denote_pure f h := by cases h

attribute [local instance] categoricalInstructions

private def raw : Primitive Event Op (Sigma Atoms) := fun op x =>
  match x with
  | .atom a => vis (.call op a.2.down) (fun n => pure (.atom ⟨⟨()⟩, ⟨n⟩⟩))
  | _ => pure .unit

private theorem compatible :
    Compatible (κ' := Atom) ⟨fun f x =>
      InstructionModel.denote (τ := Ty Atom) (ε := Bool) (m := TM) f x⟩ raw := by
  intro f x
  change vis (.call f x.down) (fun n => (pure (.atom ⟨⟨()⟩, ⟨n⟩⟩) : TM _)) =
    (vis (.call f x.down) (fun n => (pure (ULift.up n) : TM _)) >>= fun y =>
      pure (Silmaril.Isotope.Semantics.encodeValue Atoms A y))
  simp only [vis_bind, pure_bind]
  rfl

private theorem opTyped (f : Op) :
    Tm.HasType [A] (.op f (.var 0)) A := .op (.var rfl)

private def arrow (f : Op) : ofType (Φ := Op) A ⟶ ofType A :=
  ofRegion (returnOnce_typed (opTyped f))

private noncomputable def observe (f : ofType (Φ := Op) A ⟶ ofType A) :
    ULift.{1} Nat → TM (ULift.{1} Nat) :=
  ((weakITreeFunctor raw compatible).map f).of

private theorem mapArrow (f : Op) (n : Nat) :
    observe (arrow f) ⟨n⟩ =
      vis (.call f n) (fun k => pure ⟨k⟩) := by
  have := regionTypingCoherent raw compatible
  unfold observe
  rw [arrow, weakITreeFunctor_map_ofRegion,
    returnOnce_denotation K T (opTyped f) (Denotes.op (Denotes.var rfl))]
  have idArg : (λ_ ((T).obj A)).inv ≫ lookup T 0 (show At [A] 0 A from rfl) =
      𝟙 ((T).obj A) := by
    change (λ_ ((T).obj A)).inv ≫ CartesianMonoidalCategory.snd (𝟙_ (Type 1)) ((T).obj A) = _
    exact CartesianMonoidalCategory.leftUnitor_inv_snd _
  have arrowEq :
      (K).map ((λ_ ((T).obj A)).inv) ≫
          (K).map (lookup T 0 (show At [A] 0 A from rfl)) ≫
          LetIter.Semantics.Categorical.InstructionModel.denote (J := K) (M := T) f =
        LetIter.Semantics.Categorical.InstructionModel.denote (J := K) (M := T) f := by
    rw [← Functor.map_comp_assoc, idArg]
    exact Category.id_comp _
  exact congrArg (fun (g : (K).obj ((T).obj A) ⟶ (K).obj ((T).obj A)) => g.of ⟨n⟩) arrowEq

-- Both calls use the concrete functor's action on the composite Paper arrow.
-- The second operand is the actual reply to the first event.
example (n : Nat) :
    out (show TM (ULift.{1} Nat) from
      ((weakITreeFunctor raw compatible).map (arrow .read ≫ arrow .write)).of ⟨n⟩) =
    Part.some (.vis (.call .read n) (fun reply => vis (.call .write reply) (fun k => pure ⟨k⟩))) := by
  rw [Functor.map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
  change out (observe (arrow .read) ⟨n⟩ >>= observe (arrow .write)) = _
  have second : (fun reply => observe (arrow .write) (ULift.up reply)) =
      fun reply => vis (.call .write reply) (fun k => (pure (ULift.up k) : TM _)) := by
    funext reply
    exact mapArrow .write reply
  rw [mapArrow, vis_bind]
  simp only [pure_bind, out_vis]
  rw [second]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonDenotationITreeExample
