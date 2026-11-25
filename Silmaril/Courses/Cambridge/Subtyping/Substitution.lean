module

public import Silmaril.Courses.Cambridge.Subtyping.Typing
public import Silmaril.Courses.Cambridge.L3.Metatheory.Substitution

/-! # Weakening and typed substitution with subsumption

The binder operations and renaming relation are the ones used by L3.
The additional subsumption cases carry the same subtype derivation through
each induction.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Subtyping

open L3 (Ty Expr VarTypes LocTypes BoundRenaming swapFirstTwo)

theorem Typing.rename {Θ : LocTypes} {Γ Δ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (ρ : Nat → Nat) (free : Γ.free = Δ.free)
    (bound : BoundRenaming Γ.bound Δ.bound ρ) : HasType Θ Δ (e.rename ρ) T := by
  induction typed generalizing Δ ρ with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ ihl ihr => exact .add (ihl ρ free bound) (ihr ρ free bound)
  | ge _ _ ihl ihr => exact .ge (ihl ρ free bound) (ihr ρ free bound)
  | cond _ _ _ ihc ihy ihn => exact .cond (ihc ρ free bound) (ihy ρ free bound) (ihn ρ free bound)
  | skip => exact .skip
  | seq _ _ ihl ihr => exact .seq (ihl ρ free bound) (ihr ρ free bound)
  | loop _ _ iht ihb => exact .loop (iht ρ free bound) (ihb ρ free bound)
  | bvar lookup => exact .bvar (bound lookup)
  | fvar lookup => exact .fvar (free ▸ lookup)
  | lam _ ih => exact .lam (ih _ free (bound.push _))
  | app _ _ ihf iha => exact .app (ihf ρ free bound) (iha ρ free bound)
  | letE _ _ ihv ihb => exact .letE (ihv ρ free bound) (ihb _ free (bound.push _))
  | letRecFun _ _ ihf ihb =>
      exact .letRecFun (ihf _ free (BoundRenaming.push (bound.push _) _))
        (ihb _ free (bound.push _))
  | pair _ _ ihl ihr => exact .pair (ihl ρ free bound) (ihr ρ free bound)
  | fst _ ih => exact .fst (ih ρ free bound)
  | snd _ ih => exact .snd (ih ρ free bound)
  | inl _ ih => exact .inl (ih ρ free bound)
  | inr _ ih => exact .inr (ih ρ free bound)
  | matchSum _ _ _ ihe ihl ihr =>
      exact .matchSum (ihe ρ free bound)
        (ihl _ free (bound.push _)) (ihr _ free (bound.push _))
  | record _ ih => exact .record (fun i => ih i ρ free bound)
  | project i _ ih => exact .project i (ih ρ free bound)
  | ref _ ih => exact .ref (ih ρ free bound)
  | assign _ _ ihl ihr => exact .assign (ihl ρ free bound) (ihr ρ free bound)
  | deref _ ih => exact .deref (ih ρ free bound)
  | loc lookup => exact .loc lookup
  | sub _ sub ih => exact .sub (ih ρ free bound) sub

def TypedSubst (Θ : LocTypes) (Γ : List Ty) (Δ : VarTypes) (σ : Nat → Expr) : Prop :=
  ∀ {i T}, Γ[i]? = some T → HasType Θ Δ (σ i) T

theorem TypedSubst.push {Θ : LocTypes} {Γ : List Ty} {Δ : VarTypes} {σ : Nat → Expr}
    (h : TypedSubst Θ Γ Δ σ) (A : Ty) :
    TypedSubst Θ (A :: Γ) (Δ.push A) (Expr.liftSubst σ) := by
  intro i T lookup
  cases i with
  | zero => exact .bvar lookup
  | succ i =>
      exact (h (i := i) lookup).rename Nat.succ rfl (BoundRenaming.succ Δ.bound A)

/-- Simultaneous substitution preserves the type of the expression. -/
theorem Typing.subst {Θ : LocTypes} {Γ Δ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (σ : Nat → Expr) (free : Γ.free = Δ.free)
    (bound : TypedSubst Θ Γ.bound Δ σ) : HasType Θ Δ (e.subst σ) T := by
  induction typed generalizing Δ σ with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ ihl ihr => exact .add (ihl σ free bound) (ihr σ free bound)
  | ge _ _ ihl ihr => exact .ge (ihl σ free bound) (ihr σ free bound)
  | cond _ _ _ ihc ihy ihn => exact .cond (ihc σ free bound) (ihy σ free bound) (ihn σ free bound)
  | skip => exact .skip
  | seq _ _ ihl ihr => exact .seq (ihl σ free bound) (ihr σ free bound)
  | loop _ _ iht ihb => exact .loop (iht σ free bound) (ihb σ free bound)
  | bvar lookup => exact bound lookup
  | fvar lookup => exact .fvar (free ▸ lookup)
  | lam _ ih => exact .lam (ih _ free (bound.push _))
  | app _ _ ihf iha => exact .app (ihf σ free bound) (iha σ free bound)
  | letE _ _ ihv ihb => exact .letE (ihv σ free bound) (ihb _ free (bound.push _))
  | letRecFun _ _ ihf ihb =>
      exact .letRecFun (ihf _ free (TypedSubst.push (bound.push _) _))
        (ihb _ free (bound.push _))
  | pair _ _ ihl ihr => exact .pair (ihl σ free bound) (ihr σ free bound)
  | fst _ ih => exact .fst (ih σ free bound)
  | snd _ ih => exact .snd (ih σ free bound)
  | inl _ ih => exact .inl (ih σ free bound)
  | inr _ ih => exact .inr (ih σ free bound)
  | matchSum _ _ _ ihe ihl ihr =>
      exact .matchSum (ihe σ free bound)
        (ihl _ free (bound.push _)) (ihr _ free (bound.push _))
  | record _ ih => exact .record (fun i => ih i σ free bound)
  | project i _ ih => exact .project i (ih σ free bound)
  | ref _ ih => exact .ref (ih σ free bound)
  | assign _ _ ihl ihr => exact .assign (ihl σ free bound) (ihr σ free bound)
  | deref _ ih => exact .deref (ih σ free bound)
  | loc lookup => exact .loc lookup
  | sub _ sub ih => exact .sub (ih σ free bound) sub

theorem Typing.beta {Θ : LocTypes} {Γ : VarTypes} {body argument : Expr} {A B : Ty}
    (bodyType : HasType Θ (Γ.push A) body B)
    (argumentType : HasType Θ Γ argument A) : HasType Θ Γ (body.beta argument) B := by
  apply bodyType.subst (Δ := Γ) (fun | 0 => argument | i + 1 => .bvar i) rfl
  intro i T lookup
  cases i with
  | zero =>
      have same : A = T := Option.some.inj lookup
      cases same
      exact argumentType
  | succ i => exact .bvar lookup

theorem Typing.recClosure {Θ : LocTypes} {Γ : VarTypes} {body : Expr} {A B : Ty}
    (typed : HasType Θ ((Γ.push (.arr A B)).push A) body B) :
    HasType Θ Γ (body.recClosure A B) (.arr A B) := by
  apply Typing.lam
  apply Typing.letRecFun
  · exact typed.rename (DeBruijn.liftN 2 Nat.succ) rfl
      (BoundRenaming.push (BoundRenaming.push (BoundRenaming.succ Γ.bound A) (.arr A B)) A)
  · apply typed.rename (Δ := (Γ.push A).push (.arr A B)) swapFirstTwo rfl
    intro i T lookup
    cases i with
    | zero => exact lookup
    | succ i => cases i <;> exact lookup

theorem Typing.weakenLocs {Θ Θ' : LocTypes} {Γ : VarTypes} {e : Expr} {T : Ty}
    (typed : HasType Θ Γ e T) (h : Θ.Extends Θ') : HasType Θ' Γ e T := by
  induction typed with
  | loc lookup => exact .loc (h lookup)
  | project i _ ih => exact .project i ih
  | record _ ih => exact .record ih
  | int => exact .int _
  | bool => exact .bool _
  | skip => exact .skip
  | bvar lookup => exact .bvar lookup
  | fvar lookup => exact .fvar lookup
  | add _ _ ihl ihr => exact .add ihl ihr
  | ge _ _ ihl ihr => exact .ge ihl ihr
  | cond _ _ _ ihc ihy ihn => exact .cond ihc ihy ihn
  | seq _ _ ihl ihr => exact .seq ihl ihr
  | loop _ _ iht ihb => exact .loop iht ihb
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | letE _ _ ihv ihb => exact .letE ihv ihb
  | letRecFun _ _ ihf ihb => exact .letRecFun ihf ihb
  | pair _ _ ihl ihr => exact .pair ihl ihr
  | fst _ ih => exact .fst ih
  | snd _ ih => exact .snd ih
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | matchSum _ _ _ ihe ihl ihr => exact .matchSum ihe ihl ihr
  | ref _ ih => exact .ref ih
  | assign _ _ ihl ihr => exact .assign ihl ihr
  | deref _ ih => exact .deref ih

  | sub _ sub ih => exact .sub ih sub

end Silmaril.Courses.Cambridge.Subtyping
