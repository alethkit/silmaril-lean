module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Defs

/-! # Free-tree values and typed response-bearing instruction events -/

@[expose] public section

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response

universe u r

variable {α Φ : Type u} (S : Signature α Φ) {n : Nat} (sorts : Fin n → α)

abbrev Atom (a : α) := ULift.{u + 2} (Tree S sorts a)
local notation "D" => Ty.denote (Atom S sorts)

abbrev Args (f : Φ) := (i : Fin (S.arity f)) → Tree S sorts (S.arg f i)
abbrev Request := (f : Φ) × Args S sorts f

def unpackArgs : (m : Nat) → (as : Fin m → α) → D (input m as) →
    ((i : Fin m) → Tree S sorts (as i))
  | 0, _, _, i => i.elim0
  | m + 1, as, p, i =>
      Fin.cases (motive := fun j => Tree S sorts (as j)) p.1.down
        (unpackArgs m (fun j => as j.succ) p.2) i

/-- Assemble an instruction input from its atomic components. -/
def packArgs : (m : Nat) → (as : Fin m → α) →
    ((i : Fin m) → Tree S sorts (as i)) → D (input m as)
  | 0, _, _ => PUnit.unit
  | m + 1, as, xs => (⟨xs 0⟩, packArgs m (fun i => as i.succ) (fun i => xs i.succ))

def readArgs (f : Φ) (x : D (input (S.arity f) (S.arg f))) : Args S sorts f :=
  unpackArgs S sorts (S.arity f) (S.arg f) x

/-- The response takes index zero in the scope of the remainder. -/
abbrev extendSorts {m : Nat} (a : α) (slots : Fin m → α) : Fin (m + 1) → α :=
  Fin.cases a slots

/-- Place one typed response before the existing valuation. -/
def extendValues {m : Nat} {a : α} {slots : Fin m → α}
    (r : Tree S sorts a) (vars : (i : Fin m) → Tree S sorts (slots i)) :
    (i : Fin (m + 1)) → Tree S sorts (extendSorts a slots i) :=
  Fin.cases (motive := fun i => Tree S sorts (extendSorts a slots i)) r vars

/-- Assign a sorted tree to every atomic slot of a native environment. -/
def variableEnv {ε : Type r} {Γ : EffectCtx (Ty α) ε} {slots : Fin Γ.length → α}
    (hslots : ∀ i, (Γ.get i).1 = .base (slots i))
    (vars : (i : Fin Γ.length) → Tree S sorts (slots i)) : BoundEnv D Γ.toBoundCtx :=
  fun i => ((EffectCtx.get_toBoundCtx Γ i).trans (hslots i)).symm ▸ (⟨vars i⟩ : Atom S sorts _)

/-- An event retains the whole input and returns a value of the declared result sort. -/
inductive Event : Type (u + 1) → Type (u + 1) where
  | call (f : Φ) (x : Args S sorts f) : Event (Tree S sorts (S.out f))

section Effects

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

noncomputable def instructions : @InstructionModel (Ty α) D Φ (ITree.Tree (Event S sorts)) S.endpoints := by
  classical
  let instr := S.endpoints
  exact ⟨fun f x => if IsPure (⊥ : ε) f then
    ITree.ret ⟨Tree.op f (readArgs S sorts f x)⟩
    else ITree.vis (.call f (readArgs S sorts f x)) (fun r => ITree.ret ⟨r⟩)⟩

end Effects

def visibleRequest {Y X : Type (u + 2)} : ITree.Visible (Event S sorts) Y X → Option (Request S sorts)
  | .ret _ => none
  | .vis (.call f x) _ => some ⟨f, x⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response
