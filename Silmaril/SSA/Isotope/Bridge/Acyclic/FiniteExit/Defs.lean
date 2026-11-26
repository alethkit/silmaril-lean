module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.TwoExit.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Thms

/-! # Structured acyclic regions at finite ordered exit interfaces -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Acyclic

variable {τ : Type u} [TypeFormers τ]

/-- A branch selects a position in the external label list. A join's body
is outside the scope of the local entry label. -/
inductive FiniteExit (Φ : Type v) [HasTy Φ τ] (L : LCtx τ) :
    {n : Nat} → BoundCtx τ n → Type (max u v)
  | br {n : Nat} {β : BoundCtx τ n} {i : Nat} {A : τ} :
      At L i A → Operand Φ β A → FiniteExit Φ L β
  | case {n : Nat} {β : BoundCtx τ n} {A B : τ} :
      Operand Φ β (coprod A B) → FiniteExit Φ L (β.snoc A) →
      FiniteExit Φ L (β.snoc B) → FiniteExit Φ L β
  | join {n : Nat} {β : BoundCtx τ n} {A : τ} :
      Code Φ β A → FiniteExit Φ L (β.snoc A) → FiniteExit Φ L β

namespace FiniteExit

variable {Φ : Type v} [HasTy Φ τ] {L : LCtx τ} {n : Nat} {β : BoundCtx τ n}

open Region (packedExitType)

/-- Lower to the positional region syntax, keeping the original exit labels. -/
def toSSA : {n : Nat} → {β : BoundCtx τ n} → FiniteExit Φ L β → Region Φ
  | _, _, .br (i := i) _ a => .br i (Morphism.CaseSSA.erase a.1)
  | _, _, .case e l r => .case (Morphism.CaseSSA.erase e.1) l.toSSA r.toSSA
  | _, _, .join (A := A) a b => (a.toSSA 0).linkExits [A] (fun _ => b.toSSA)

/-- Tag an exactly typed operand by the position of its outward label. -/
def tag (L : LCtx τ) (i : Nat) {A : τ} (hi : At L i A)
    (a : Operand Φ β A) : Operand Φ β (packedExitType L) :=
  match L, i with
  | [], _ => nomatch hi
  | _ :: _, 0 => Option.some.inj hi ▸ ⟨.inl a.1, .inl a.2⟩
  | _ :: L, i + 1 =>
    let b := tag L i hi a
    ⟨.inr b.1, .inr b.2⟩

/-- Encode each branch as a return of its tagged payload while preserving
the case and join structure. -/
def encode : {n : Nat} → {β : BoundCtx τ n} → FiniteExit Φ L β →
    Code Φ β (packedExitType L)
  | _, _, .br (i := i) hi a => .br (tag L i hi a)
  | _, _, .case e l r => .case e l.encode r.encode
  | _, _, .join a b => .join a b.encode

/-- Route the newest tagged value to the native exits. An impossible empty
tail uses an abort expression at a valid outward label, so the decoder has
no recursive CFG even on its empty summand. -/
def decodeBody {K : LCtx τ} {j : Nat} {D : τ} (fallback : At K j D) :
    (L : LCtx τ) → {ρ : Nat → Nat} → Ren L K ρ →
    {n : Nat} → (β : BoundCtx τ n) → FiniteExit Φ K (β.snoc (packedExitType L))
  | [], _, _, _, _ => .br fallback ⟨.abort (.bv 0), .abort .bv⟩
  | A :: L, ρ, ren, _, β =>
    .case ⟨.bv 0, .bv⟩ (.br (ren (rfl : At (A :: L) 0 A)) ⟨.bv 0, .bv⟩)
      (decodeBody fallback L (ρ := fun i => ρ (i + 1))
        (fun _ _ hi => ren hi) (β.snoc (packedExitType (A :: L))))

/-- Decode a packed result at any nonempty outward interface. -/
def decode : {L : LCtx τ} → L ≠ [] →
    Code Φ β (packedExitType L) → FiniteExit Φ L β
  | [], nonempty, _ => False.elim (nonempty rfl)
  | A :: L, _, c => .join c (decodeBody (Φ := Φ) (rfl : At (A :: L) 0 A)
      (A :: L) (SSA.Ren.id (A :: L)) β)

end FiniteExit

namespace TwoExit

variable {Φ : Type v} [HasTy Φ τ] {A B : τ}

/-- Embed the binary fragment while retaining the same two native labels. -/
def toFinite : {n : Nat} → {β : BoundCtx τ n} → TwoExit Φ A B β → FiniteExit Φ [A, B] β
  | _, _, .left a => .br (i := 0) rfl a
  | _, _, .right b => .br (i := 1) rfl b
  | _, _, .case e l r => .case e l.toFinite r.toFinite
  | _, _, .dispatch c =>
    .join c (.case ⟨.bv 0, .bv⟩
      (.br (i := 0) rfl ⟨.bv 0, .bv⟩) (.br (i := 1) rfl ⟨.bv 0, .bv⟩))

end TwoExit
end Silmaril.Isotope.LambdaSSA.Acyclic
