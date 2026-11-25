module

public import Silmaril.Semantics.ITree.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.Native.Thms

/-! # Free value trees for finite-arity source signatures -/

@[expose] public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.Semantics Silmaril.Elgot
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree

universe u r

structure Signature (α : Type u) (Φ : Type u) where
  arity : Φ → Nat
  arg : (f : Φ) → Fin (arity f) → α
  out : Φ → α

variable {α : Type u} {Φ : Type u} (S : Signature α Φ)

/-- A right-associated product of argument sorts ending in unit. -/
def input : (n : Nat) → (Fin n → α) → Ty α
  | 0, _ => .unit
  | n + 1, as => .product (.base (as 0)) (input n (fun i => as i.succ))

/-- Each instruction takes a tuple of atoms and returns an atom. -/
@[instance_reducible] def Signature.endpoints : HasTy Φ (Ty α) :=
  ⟨fun f => input (S.arity f) (S.arg f), fun f => .base (S.out f)⟩

/-- Free many-sorted term algebra. The variable constructors distinguish the
slots of the input context, including multiple slots of one sort. -/
inductive Tree {n : Nat} (sorts : Fin n → α) : α → Type (u + 1)
  | var (i : Fin n) : Tree sorts (sorts i)
  | op (f : Φ) (args : (i : Fin (S.arity f)) → Tree sorts (S.arg f i)) : Tree sorts (S.out f)

variable {n : Nat} {sorts : Fin n → α}

def arguments (F : α → Type (u + 1)) :
    (k : Nat) → (as : Fin k → α) → Ty.denote F (input k as) → ((i : Fin k) → F (as i))
  | 0, _, _, i => i.elim0
  | k + 1, as, p, i => Fin.cases (motive := fun j => F (as j)) p.1
      (arguments F k (fun j => as j.succ) p.2) i

def tuple (F : α → Type (u + 1)) :
    (k : Nat) → (as : Fin k → α) → ((i : Fin k) → F (as i)) → Ty.denote F (input k as)
  | 0, _, _ => PUnit.unit
  | k + 1, as, xs => (xs 0, tuple F k (fun j => as j.succ) (fun j => xs j.succ))

def Tree.interpret (F : α → Type (u + 1))
    (ops : (f : Φ) → ((i : Fin (S.arity f)) → F (S.arg f i)) → F (S.out f))
    (vars : (i : Fin n) → F (sorts i)) :
    {a : α} → Tree S sorts a → F a
  | _, .var i => vars i
  | _, .op f xs => ops f (fun i => Tree.interpret F ops vars (xs i))

def nativeTuple {n : Nat} : (k : Nat) → (Fin k → Tm Empty Φ n) → Tm Empty Φ n
  | 0, _ => .unit
  | k + 1, xs => .pair (xs 0) (nativeTuple k (fun i => xs i.succ))

def sourceTuple : (k : Nat) → (Fin k → Expr Φ) → Expr Φ
  | 0, _ => .unit
  | k + 1, xs => .pair (xs 0) (sourceTuple k (fun i => xs i.succ))

def Tree.native : {a : α} → Tree S sorts a → Tm Empty Φ n
  | _, .var i => .bv i
  | _, .op f xs => .op f (nativeTuple (S.arity f) (fun i => Tree.native (xs i)))

def Tree.source : {a : α} → Tree S sorts a → Expr Φ
  | _, .var i => .var i.val
  | _, .op f xs => .op f (sourceTuple (S.arity f) (fun i => Tree.source (xs i)))

section Typed

variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {Γ : EffectCtx (Ty α) ε} {sorts : Fin Γ.length → α}

local notation "D" => Ty.denote (Tree S sorts)

/-- Every operation in the tree is declared bottom-effect. -/
def DeclaredPure {n : Nat} {sorts : Fin n → α} :
    {a : α} → Tree S sorts a → Prop
  | _, .var _ => True
  | _, .op f args => IsPure (⊥ : ε) f ∧ ∀ i, DeclaredPure (args i)

inductive Event (Φ : Type u) : Type u → Type u
  | stop (f : Φ) (observation : Bool) : Event Φ PEmpty

abbrev ObserveInput := (f : Φ) → D (input (S.arity f) (S.arg f)) → Bool

/-- Evaluate pure instructions in the free value algebra. An effectful instruction
emits its symbol and the chosen input observation, with no response. -/
noncomputable def instructions (observe : ObserveInput (sorts := sorts) S) :
    @InstructionModel (Ty α) D Φ (ITree.Tree (Event Φ)) S.endpoints := by
  classical
  let instr := S.endpoints
  exact ⟨fun f x => if IsPure (⊥ : ε) f then
    ITree.ret (Tree.op f (arguments _ _ _ x))
    else ITree.vis (Event.stop f (observe f x)) (fun z : PEmpty => z.elim)⟩

end Typed

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree
