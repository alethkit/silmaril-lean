module

import Silmaril.SSA.RVSDG.LambdaSSA.Theta.Categorical.Thms
import Silmaril.SSA.RVSDG.Theta.Categorical.Thms
import Silmaril.Raw.SSA.Isotope.LetIter.Semantics.Categorical.Kleisli

namespace Silmaril.SSA.RVSDG.LambdaSSA.Theta.Tests

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel ofTypeModel)

private abbrev Code := Silmaril.Ty Unit
private abbrev number : Code := .base ()
private abbrev Op := Option Nat

local instance : HasTy Op Code := ⟨fun _ => number, fun _ => .coprod number number⟩

private def step (limit : Op) : Step Op number := ⟨limit, rfl, rfl⟩

private def next (limit : Op) (n : Nat) : Nat ⊕ Nat :=
  match limit with
  | some bound => if n + 1 < bound then .inr (n + 1) else .inl (n + 1)
  | none => .inr (n + 1)

private abbrev V := Silmaril.Ty.denote (fun _ : Unit => Nat)
private noncomputable abbrev M := ofTypeModel V
private noncomputable abbrev J := RVSDG.Theta.partJ.{0}

private def prim (op : Op) : M.obj (instrSrc op) ⟶ M.obj (instrTrg op) :=
  TypeCat.ofHom (next op)

private noncomputable local instance : InstructionModel J M Op :=
  ⟨fun op => J.map (prim op)⟩

private def lowered (limit : Op) :=
  lower (SSAForm.loop (step limit))

private def raised (limit : Op) :=
  raise (RVForm.loop (step limit))

example : (raised (some 3)).1 = region (some 3) := rfl
example : (lowered (some 3)).1 = graph (step (some 3)) := rfl

private def runtime : RVSDG.Model (Opcode (τ := Code) Op) where
  value := V
  state s := s.elim
  run
    | .step s, .cons n .nil =>
      match next s.op (cast (congrArg V s.input.symm) n) with
      | .inl a => .cons (ULift.up 0) (.cons (cast (congrArg V s.input) a) .nil)
      | .inr a => .cons (ULift.up 1) (.cons (cast (congrArg V s.input) a) .nil)

private abbrev OpModel := Categorical.Model (Opcode (τ := Code) Op) (Type)
private abbrev Prim := ∀ {ins outs}, Opcode (τ := Code) Op ins outs →
  ((Categorical.Model.ofRuntime runtime).ports ins ⟶ (Categorical.Model.ofRuntime runtime).ports outs)

private def withPrim (f : Prim) : OpModel :=
  ⟨Categorical.typeSelectors, V, fun s => s.elim, fun op => f op⟩

private theorem primitives_eq :
    @Eq Prim (fun {ins outs} op => (valueModel M prim Categorical.typeSelectors).primitive (ins := ins) (outs := outs) op)
      (fun {ins outs} op => (Categorical.Model.ofRuntime runtime).primitive (ins := ins) (outs := outs) op) := by
  funext inputs outputs opcode
  cases opcode with
  | @step A s =>
    obtain ⟨op, source, target⟩ := s
    change number = _ at source
    subst A
    ext ⟨n, pad⟩
    change Nat at n
    change PUnit at pad
    cases pad
    change (encodeStep Categorical.typeSelectors Nat)
      ((Types.binaryCoproductIso Nat Nat).inv (next op n)) =
        Categorical.pack (match next op n with
        | .inl a => (.cons (ULift.up (0 : Fin 2)) (.cons a .nil) :
            Tuple runtime.Val (results number))
        | .inr a => .cons (ULift.up (1 : Fin 2)) (.cons a .nil))
    cases next op n <;>
      simp only [encodeStep, Types.binaryCoproductIso_inl_comp_inv_apply,
        Types.binaryCoproductIso_inr_comp_inv_apply, ← types_comp_apply, coprod.inl_desc,
        coprod.inr_desc] <;> rfl

private def input (n : Nat) : Tuple runtime.Val (carried number) := .cons n .nil

example : ((lowered (some 3)).1.denote J (valueModel M prim Categorical.typeSelectors)).of
    (Categorical.pack (input 0)) = Part.some (Categorical.pack (input 3)) := by
  change ((lowered (some 3)).1.denote J (withPrim (fun op =>
    (valueModel M prim Categorical.typeSelectors).primitive op))).of _ = _
  rw [primitives_eq]
  exact ((graph (step (some 3))).denotePart_eq_some runtime _ _).2
    (.again (next := input 1) rfl (.again (next := input 2) rfl (.stop rfl)))

example : ((lowered none).1.denote J (valueModel M prim Categorical.typeSelectors)).of
    (Categorical.pack (input 0)) = Part.none := by
  change ((lowered none).1.denote J (withPrim (fun op =>
    (valueModel M prim Categorical.typeSelectors).primitive op))).of _ = _
  rw [primitives_eq]
  exact ((graph (step none)).denotePart_eq_none runtime _).2
    ⟨input, rfl, fun _ => rfl⟩

example (limit : Op) :
    RegionDenotes J M (lowered limit).2.typing
      (J.map (entryMap M number) ≫ (lowered limit).1.denote J (valueModel M prim Categorical.typeSelectors) ≫
        J.map ((CategoryTheory.MonoidalCategory.rightUnitor (M.obj number)).hom ≫
          labelInject M (L := [number]) 0 rfl)) :=
  (lowered limit).2.preserves J M prim (fun _ => rfl) Categorical.typeSelectors

end Silmaril.SSA.RVSDG.LambdaSSA.Theta.Tests
