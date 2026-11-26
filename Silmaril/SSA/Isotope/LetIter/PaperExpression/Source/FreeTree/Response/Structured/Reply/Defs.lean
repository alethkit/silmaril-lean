module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Defs

/-! # Constructor observations of primitive replies -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm Derivation)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

universe u v w

variable {α : Type u}

/-- The constructor shape of a reply, with one fresh slot per atomic field.
A product concatenates its slots and a sum supplies the selected payload
slots only. An empty type has no reply shape. -/
inductive ReplyShape : {n : Nat} → (Fin n → α) → Ty α → Type u
  | atom (a : α) : ReplyShape (fun _ : Fin 1 => a) (.base a)
  | unit : ReplyShape (Fin.elim0 : Fin 0 → α) .unit
  | pair {n m : Nat} {ss : Fin n → α} {ts : Fin m → α} {A B : Ty α}
      (left : ReplyShape ss A) (right : ReplyShape ts B) :
      ReplyShape (Fin.addCases ss ts) (.product A B)
  | inl {n : Nat} {ss : Fin n → α} {A B : Ty α} (shape : ReplyShape ss A) :
      ReplyShape ss (.coprod A B)
  | inr {n : Nat} {ss : Fin n → α} {A B : Ty α} (shape : ReplyShape ss B) :
      ReplyShape ss (.coprod A B)

namespace ReplyShape

/-- Interpret the constructor shape at sorted values for its fresh slots. -/
def denote (V : α → Type v) :
    {n : Nat} → {ss : Fin n → α} → {A : Ty α} →
      ReplyShape ss A → ((i : Fin n) → V (ss i)) → Ty.denote V A
  | _, _, _, .atom _, vars => vars 0
  | _, _, _, .unit, _ => PUnit.unit
  | _, _, _, .pair (n := n) (m := m) (ss := ss) (ts := ts) l r, vars =>
      (l.denote V (fun i => cast (congrArg V (Fin.addCases_left (motive := fun _ => α) (left := ss) (right := ts) i))
        (vars (i.castAdd m))),
       r.denote V (fun i => cast (congrArg V (Fin.addCases_right (motive := fun _ => α) (left := ss) (right := ts) i))
         (vars (i.natAdd n))))
  | _, _, _, .inl s, vars => Sum.inl (s.denote V vars)
  | _, _, _, .inr s, vars => Sum.inr (s.denote V vars)

/-- Render a reply shape using chosen positions of its fresh slots. -/
def source {Φ : Type w} {m : Nat} :
    {n : Nat} → {ss : Fin n → α} → {A : Ty α} → ReplyShape ss A → (Fin n → Fin m) → Expr Φ
  | _, _, _, .atom _, place => .var (place 0)
  | _, _, _, .unit, _ => .unit
  | _, _, _, .pair (n := n) (m := m) l r, place =>
      .pair (l.source (fun i => place (i.castAdd m))) (r.source (fun i => place (i.natAdd n)))
  | _, _, _, .inl s, place => .inl (s.source place)
  | _, _, _, .inr s, place => .inr (s.source place)

/-- The native constructor rendering uses exactly the same slot positions. -/
@[reducible] def native {Φ : Type w} {m : Nat} :
    {n : Nat} → {ss : Fin n → α} → {A : Ty α} → ReplyShape ss A → (Fin n → Fin m) → Tm Empty Φ m
  | _, _, _, .atom _, place => .bv (place 0)
  | _, _, _, .unit, _ => .unit
  | _, _, _, .pair (n := n) (m := m) l r, place =>
      .pair (l.native (fun i => place (i.castAdd m))) (r.native (fun i => place (i.natAdd n)))
  | _, _, _, .inl s, place => .inl (s.native place)
  | _, _, _, .inr s, place => .inr (s.native place)

/-- Build proof-relevant native typing at any embedding of the slots. -/
def derivation {Φ : Type w} [HasTy Φ (Ty α)] {m : Nat} {β : BoundCtx (Ty α) m} :
    {n : Nat} → {ss : Fin n → α} → {A : Ty α} → (s : ReplyShape ss A) →
      (place : Fin n → Fin m) → (∀ i, β.get (place i) = .base (ss i)) →
        Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β (s.native place) A
  | _, _, _, .atom _, p, hs => cast (congrArg (Derivation Φ (Ctx.nil : Ctx Empty (Ty α)) β (.bv (p 0))) (hs 0))
        (Derivation.bv (ι := p 0))
  | _, _, _, .unit, _, _ => .unit
  | _, _, _, .pair (n := n) (m := m) (ss := ss) (ts := ts) l r, p, hs =>
      .pair (l.derivation (fun i => p (i.castAdd m))
        (fun i => (hs _).trans (congrArg Ty.base (Fin.addCases_left (motive := fun _ => α) (left := ss) (right := ts) i))))
        (r.derivation (fun i => p (i.natAdd n))
          (fun i => (hs _).trans (congrArg Ty.base (Fin.addCases_right (motive := fun _ => α) (left := ss) (right := ts) i))))
  | _, _, _, .inl s, p, hs => .inl (s.derivation p hs)
  | _, _, _, .inr s, p, hs => .inr (s.derivation p hs)

end ReplyShape
end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
