module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Thms

/-! # One visible request per round of feedback -/

@[expose] public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback

universe u v

variable {α Φ : Type u} [HasTy Φ (Ty α)] {V : α → Type u} {f : Φ}

/-- The state specifies the request argument. Each reply either returns a
value or selects the next state. -/
structure Machine (V : α → Type u) (f : Φ) (S B : Type v) where
  request : S → Ty.denote V (instrSrc f)
  reply : S → Ty.denote V (instrTrg f) → B ⊕ S

variable {S T B : Type v}

def Machine.step (M : Machine V f S B) (s : S) : ITree.Tree (Event (Φ := Φ) V) (B ⊕ S) :=
  ITree.vis (.call f (M.request s)) (fun r => ITree.ret (M.reply s r))

noncomputable def Machine.run (M : Machine V f S B) : S → ITree.Tree (Event (Φ := Φ) V) B :=
  Silmaril.Elgot.iter M.step

/-- States that can be reached by finitely many repeat replies. -/
inductive Machine.Reaches (M : Machine V f S B) (initial : S) : S → Prop
  | initial : Reaches M initial initial
  | after_reply {s t : S} (reach : Reaches M initial s) (reply : Ty.denote V (instrTrg f))
      (edge : M.reply s reply = .inr t) : Reaches M initial t

/-- A state map preserves the request and each typed reply. -/
def Commutes (L : Machine V f S B) (R : Machine V f T B) (h : S → T) : Prop :=
  ∀ s, L.request s = R.request (h s) ∧
    ∀ r, Sum.map id h (L.reply s r) = R.reply (h s) r

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback
