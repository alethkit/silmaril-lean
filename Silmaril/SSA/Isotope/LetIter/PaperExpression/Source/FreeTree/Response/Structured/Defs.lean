module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
public import Silmaril.Semantics.ITree.Thms

/-! # Weak interaction trees over arbitrary typed primitive requests -/

@[expose] public section

open Silmaril.Isotope.Semantics Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured

universe u v r

variable {α Φ : Type u} [HasTy Φ (Ty α)] (V : α → Type u)

/-- Record the original primitive and its full typed input. The response
index retains the declared result, including empty and compound types. -/
inductive Event : Type u → Type u
  | call (f : Φ) (arg : Ty.denote V (instrSrc f)) : Event (Ty.denote V (instrTrg f))

abbrev Request := (f : Φ) × Ty.denote V (instrSrc f)

/-- Observe a visible request, a return, or silent divergence via `Part`. -/
noncomputable def headRequest {A : Type v} (t : ITree.Tree (Event (Φ := Φ) V) A) :
    _root_.Part (Option (Request (Φ := Φ) V)) :=
  (ITree.out t).map (fun
    | .ret _ => none
    | .vis (.call f arg) _ => some ⟨f, arg⟩)

/-- The interaction-tree monad lives one universe above the event values. -/
abbrev Lifted (a : α) := ULift.{u + 1} (V a)

/-- Lower a monadic value to the smaller event universe, preserving all
constructor tags and fields. Its inverse admits replies to the monad. -/
def toSmall : (A : Ty α) → Ty.denote (Lifted V) A ≃ Ty.denote V A
  | .base _ => _root_.Equiv.ulift
  | .product A B => _root_.Equiv.prodCongr (toSmall A) (toSmall B)
  | .coprod A B => _root_.Equiv.sumCongr (toSmall A) (toSmall B)
  | .unit => ⟨fun _ => PUnit.unit, fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  | .empty => ⟨PEmpty.elim, PEmpty.elim, (fun x => by cases x), (fun x => by cases x)⟩

variable {ε : Type r} [HasEff Φ ε] [Bot ε]

/-- Total interpretations for bottom-pure primitives on the given set
carriers. These maps are an input to the model. -/
def PureMaps (F : α → Type v) :=
  ∀ f : Φ, IsPure (⊥ : ε) f → Ty.denote F (instrSrc f) → Ty.denote F (instrTrg f)

/-- Bottom-pure instructions return via their supplied maps. Every other
instruction exposes a request before returning its response. -/
noncomputable def instructions (P : PureMaps (Φ := Φ) (ε := ε) V) :
    InstructionModel (Ty.denote (Lifted V)) Φ (ITree.Tree (Event (Φ := Φ) V)) := by
  classical
  exact ⟨fun f x =>
    let arg := toSmall V (instrSrc f) x
    let liftReply := (toSmall V (instrTrg f)).symm
    if hf : IsPure (⊥ : ε) f then ITree.ret (liftReply (P f hf arg))
    else ITree.vis (.call f arg) (fun r => ITree.ret (liftReply r))⟩

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured
