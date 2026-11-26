module

public import Silmaril.Semantics.ITree.Kleisli.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Kleisli.Thms

/-! # Typed packed programs in the ordered weak-tree model -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered

open CategoryTheory
open Silmaril.Elgot.ITree (WeakKleisli)
open scoped Silmaril.Elgot.ITree.WeakKleisli
open Silmaril.Isotope.Morphism (SignatureMap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Isotope.Semantics (encodeValue)

universe u v w

variable {κ : Type (u + 1)} [AtomValues κ]

attribute [local instance] typeModel categoricalInstructions

local notation "V" => AtomValues.carrier (κ := κ)
local notation "Interp" => Ty.denote V

/-- A model keeps the two existing interpreters and their typed compatibility,
in one event signature and with a common interpretation of atomic sorts. -/
structure Model (Events : Type u → Type u) (Φ : Type v) [HasTy Φ (Ty κ)] [HasEff Φ Bool] where
  instructions : InstructionModel Φ (Ty κ) Bool (ModelTree Events)
  raw : Primitive Events Φ (Sigma V)
  compatible : let _ := instructions
    Compatible (κ' := κ)
      ⟨fun f x => InstructionModel.denote (τ := Ty κ) (ε := Bool) (m := ModelTree Events) f x⟩ raw

/-- An exactly typed singleton region, including the representative produced
by packing a capture-free finite CFG. -/
structure Program (Φ : Type v) [HasTy Φ (Ty κ)] (A B : Ty κ) where
  code : Region Φ
  typed : Region.HasType [A] code [B]

variable {Events : Type u → Type u} {Φ : Type v} {Ψ : Type w}
  [HasTy Φ (Ty κ)] [HasEff Φ Bool] [HasTy Ψ (Ty κ)] [HasEff Ψ Bool] {A B : Ty κ}

local notation "SigMap" => SignatureMap Φ Ψ (Ty κ) (Ty κ) Bool Bool

/-- Relabel the written operations of the existing typed region. -/
def Program.map (p : Program Φ A B) (g : SigMap) (types : g.ty = id) : Program Ψ A B :=
  ⟨p.code.mapInstr g.instr, p.typed.mapInstr g.instr
    ⟨fun f => (g.source f).trans (congrFun types _),
      fun f => (g.target f).trans (congrFun types _)⟩⟩

/-- Use the literal typed singleton representative of the packed execution. -/
def Program.ofCFG {blocks exits : Nat} {R : Fin blocks → Ty κ} {D : Fin exits → Ty κ}
    {g : FiniteCFG Φ blocks exits 0} (h : g.HasType .nil R D) :
    Program Φ Silmaril.unit (Region.packedExitType (List.ofFn D)) :=
  ⟨(FiniteCFG.packedExecutionRegion h).renameVars Nat.succ,
    (FiniteCFG.packedExecution_valueBranches h).hasType⟩

/-- The existing typed singleton denotation, with its ordinary Kleisli hom
given the pointwise trace order. -/
noncomputable abbrev Program.denote (M : Model (κ := κ) Events Φ) (p : Program Φ A B) :
    (typeJ (m := ModelTree Events)).obj (Interp A) ⟶
      (typeJ (m := ModelTree Events)).obj (Interp B) :=
  let _ := M.instructions
  Categorical.denoteSingletonRegion (typeJ (m := ModelTree Events))
    (Categorical.ofMonadicTypeModel (τ := Ty κ)) p.typed

/-- A directed sentence is satisfied at all typed inputs in the model. -/
def Model.Satisfies (M : Model (κ := κ) Events Φ) (p q : Program Φ A B) : Prop :=
  p.denote M ≤ q.denote M

private theorem cast_pure {X Y : Type (u + 1)} (h : X = Y) (x : X) :
    cast (congrArg (ModelTree Events) h) (pure x) =
      (pure (cast h x) : ModelTree Events Y) := by
  cases h
  rfl

/-- Restrict typed primitives along a type-identity signature map that
preserves bottom effect. Use its exact profile equations to cast the inputs,
results and purity witnesses. -/
@[instance_reducible] def Model.reductInstructions (M : Model (κ := κ) Events Ψ)
    (g : SigMap) (types : g.ty = id) (bottom : g.eff ⊥ = ⊥) :
    InstructionModel Φ (Ty κ) Bool (ModelTree Events) where
  denote f x :=
    cast (congrArg (fun T => ModelTree Events (Interp T)) ((g.target f).trans (congrFun types _)))
      (M.instructions.denote (g.instr f)
        (cast (congrArg Interp ((g.source f).trans (congrFun types _)).symm) x))
  denotePure f hf x :=
    cast (congrArg Interp ((g.target f).trans (congrFun types _)))
      (M.instructions.denotePure (g.instr f) ((g.effect f).trans ((congrArg g.eff hf).trans bottom))
        (cast (congrArg Interp ((g.source f).trans (congrFun types _)).symm) x))
  denote_pure f hf x := by
    rw [M.instructions.denote_pure (g.instr f) ((g.effect f).trans ((congrArg g.eff hf).trans bottom))]
    exact cast_pure (congrArg Interp ((g.target f).trans (congrFun types _))) _

end Silmaril.Isotope.LambdaSSA.Semantics.Interaction.Typed.Ordered
