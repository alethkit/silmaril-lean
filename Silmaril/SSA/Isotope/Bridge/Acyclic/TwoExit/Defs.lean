module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

/-! # Structured acyclic code with two native exits -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic

open LetCase.LocallyNameless

variable {τ : Type u} [TypeFormers τ]

/-- A structured case tree with two distinct positional exits. The dispatch
constructor runs any existing single-exit acyclic code and sends the two
payload tags to different outward labels. -/
inductive TwoExit (Φ : Type v) [HasTy Φ τ] (A B : τ) :
    {n : Nat} → BoundCtx τ n → Type (max u v)
  | left {n : Nat} {β : BoundCtx τ n} : Operand Φ β A → TwoExit Φ A B β
  | right {n : Nat} {β : BoundCtx τ n} : Operand Φ β B → TwoExit Φ A B β
  | case {n : Nat} {β : BoundCtx τ n} {X Y : τ} :
      Operand Φ β (coprod X Y) → TwoExit Φ A B (β.snoc X) →
      TwoExit Φ A B (β.snoc Y) → TwoExit Φ A B β
  | dispatch {n : Nat} {β : BoundCtx τ n} : Code Φ β (coprod A B) → TwoExit Φ A B β

namespace TwoExit

variable {Φ : Type v} [HasTy Φ τ] {A B : τ}

/-- A binary decoder has two outward labels and no local feedback. -/
def decoder : Region Φ :=
  .case (.var 0) (.br 0 (.var 0)) (.br 1 (.var 0))

/-- Read the code in the native region syntax at the exit context `[A, B]`. -/
def toSSA : {n : Nat} → {β : BoundCtx τ n} → TwoExit Φ A B β → Region Φ
  | _, _, .left a => .br 0 (Morphism.CaseSSA.erase a.1)
  | _, _, .right b => .br 1 (Morphism.CaseSSA.erase b.1)
  | _, _, .case e l r => .case (Morphism.CaseSSA.erase e.1) l.toSSA r.toSSA
  | _, _, .dispatch c => (c.toSSA 0).linkExits [coprod A B] (fun _ => decoder)

/-- Encode each of the two native labels by its own coproduct injection. -/
def encode : {n : Nat} → {β : BoundCtx τ n} → TwoExit Φ A B β → Code Φ β (coprod A B)
  | _, _, .left a => .br ⟨.inl a.1, .inl a.2⟩
  | _, _, .right b => .br ⟨.inr b.1, .inr b.2⟩
  | _, _, .case e l r => .case e l.encode r.encode
  | _, _, .dispatch c => c

/-- Decoding an encoded single-exit computation uses the actual native
binary dispatcher. -/
abbrev decode {n : Nat} {β : BoundCtx τ n} (c : Code Φ β (coprod A B)) : TwoExit Φ A B β :=
  .dispatch c

/-- Reify an exact LetCase operand with a chosen binary result and decode
its two tags into actual native exits. -/
def decodeLetCase {n : Nat} {β : BoundCtx τ n}
    (a : Operand Φ β (coprod A B)) : TwoExit Φ A B β :=
  decode (Code.ofLetCase a.2)

end TwoExit
end Silmaril.Isotope.LambdaSSA.Acyclic
