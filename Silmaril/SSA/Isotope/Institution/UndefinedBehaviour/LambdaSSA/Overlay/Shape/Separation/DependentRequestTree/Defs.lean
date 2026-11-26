module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Request trees with key-indexed exact finite replies -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree

open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (pack)
open LambdaSSA.Region (packedExitType)
open TwoRequest (Exit Exits exit_type)

universe u

/-- For each key, the native opcode has one specified constructor argument
and returns the packed sum of its ordered reply payload types. -/
structure RequestSignature (Φ : Type u) [HasTy Φ Syntax.Ty] where
  replies : Φ → List Syntax.Ty
  argument : {Γ : List Syntax.Ty} → (f : Φ) → Syntax.Expr Γ (instrSrc f)
  target : ∀ f, instrTrg f = packedExitType (replies f)

variable {Φ : Type u} {R : Φ → List Syntax.Ty}

/-- Each tag gets its own continuation. The empty reply list defines a
pending request with no successful branch. -/
inductive Tree (R : Φ → List Syntax.Ty) where
  | stop (exit : Exit)
  | ask (f : Φ) (arms : Fin (R f).length → Tree R)

def Tree.depth : Tree R → Nat
  | .stop _ => 0
  | .ask _ arms => (Finset.univ.sup fun i => (arms i).depth) + 1

def Tree.region [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) :
    Tree S.replies → {Γ : List Syntax.Ty} → Overlay.Region Φ Γ Exits
  | .stop .ub, _ => .ub
  | .stop (.ret i), _ => CFG.jump (L := Exits) i (exit_type i) .unit
  | .ask f arms, _ => .lsubst (CFG.Dependent.packedRequest f (S.argument f) (S.target f))
      (fun i => (arms i).region S)

/-- Equal requests compare on tags with an inhabitable exact payload.
Distinct keys are observable even when neither can return. -/
def Tree.Refines : Tree R → Tree R → Prop
  | .stop a, .stop b => a.Refines b
  | .ask _ _, .stop .ub => True
  | .ask f arms, .ask g next => ∃ same : f = g, ∀ i,
      Nonempty (Syntax.Payload ((R f).get i)) → (arms i).Refines (next (same ▸ i))
  | _, _ => False

inductive Action (R : Φ → List Syntax.Ty) (f : Φ) (n : Nat) where
  | reply (i : Fin (R f).length) (payload : Syntax.Payload ((R f).get i)) (final : Fin n)
  | fault (final : Fin n)
  | diverge

abbrev Handler (R : Φ → List Syntax.Ty) (n : Nat) := (f : Φ) → Fin n → Action R f n

def RequestSignature.primitives [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) {n : Nat}
    (h : Handler S.replies n) : Syntax.Primitives Φ n := fun f _ s =>
  match h f s with
  | .reply i a t => .ret (cast (congrArg Syntax.Payload (S.target f).symm) (pack ⟨i, a⟩)) t
  | .fault t => .fault t
  | .diverge => .diverge

abbrev RequestSignature.model [HasTy Φ Syntax.Ty] (S : RequestSignature Φ) {n : Nat} (h : Handler S.replies n) :=
  Syntax.model (S.primitives h) Syntax.emptyBindings

def Tree.execute {n : Nat} (h : Handler R n) : Tree R → Fin n → Result 2 n
  | .stop e, s => e.result s
  | .ask f arms, s =>
    match h f s with
    | .reply i _ t => (arms i).execute h t
    | .fault t => .fault t
    | .diverge => .diverge

/-- A prefix records actual typed replies. The last state can fault on a
selected key, including a key with an empty reply list. -/
inductive Prefix (R : Φ → List Syntax.Ty) : Nat → Type u
  | stop (fault : Option Φ) : Prefix R 0
  | step {n : Nat} (f : Φ) (i : Fin (R f).length) (a : Syntax.Payload ((R f).get i))
      (rest : Prefix R n) : Prefix R (n + 1)

def Prefix.handler [DecidableEq Φ] : {n : Nat} → Prefix R n → Handler R (n + 1)
  | _, .stop fault => fun f _ => if fault = some f then .fault 0 else .diverge
  | _, .step f i a rest => fun g s =>
    Fin.cases
      (if same : f = g then same ▸ Action.reply i a (Fin.succ 0) else .diverge)
      (fun t =>
        match rest.handler g t with
        | .reply j b u => .reply j b u.succ
        | .fault u => .fault u.succ
        | .diverge => .diverge) s

theorem Prefix.handler_succ [DecidableEq Φ] {n : Nat} (rest : Prefix R n) (f g : Φ)
    (i : Fin (R f).length) (a : Syntax.Payload ((R f).get i)) (s : Fin (n + 1)) :
    (Prefix.step f i a rest).handler g s.succ =
      match rest.handler g s with
      | .reply j b t => .reply j b t.succ
      | .fault t => .fault t.succ
      | .diverge => .diverge := rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree
