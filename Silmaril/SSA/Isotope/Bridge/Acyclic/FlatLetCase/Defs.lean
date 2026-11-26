module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.Thms

/-! # Ranked flat tables to structured acyclic code and LetCase -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase

open Positional
open Positional.Capture (Scope)
open LetCase.LocallyNameless (Derivation)
open SSA.FiniteSum (append)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits n m : Nat} {β : BoundCtx τ n} {γ : BoundCtx τ m}
  {R : Fin blocks → τ} {D : Fin exits → τ}

/-- Typed operands on the written flat body. The index fixes its literal
syntax, including the product decoder and both case branches. -/
inductive Body (Φ : Type v) [HasTy Φ τ] {labels : Nat} (L : Fin labels → τ) :
    {n : Nat} → BoundCtx τ n → Flat Φ labels n → Type (max u v) where
  | br {n : Nat} {γ : BoundCtx τ n} (i : Fin labels) (a : Operand Φ γ (L i)) :
      Body Φ L γ (.br i a.1)
  | let₁ {n : Nat} {γ : BoundCtx τ n} {A : τ} (a : Operand Φ γ A) {t : Flat Φ labels (n + 1)}
      (tail : Body Φ L (γ.snoc A) t) : Body Φ L γ (.let₁ a.1 t)
  | let₂ {n : Nat} {γ : BoundCtx τ n} {A B : τ} (a : Operand Φ γ (product A B))
      {t : Flat Φ labels (n + 2)} (tail : Body Φ L ((γ.snoc A).snoc B) t) :
      Body Φ L γ (.let₂ a.1 t)
  | case {n : Nat} {γ : BoundCtx τ n} {A B : τ} (e : Operand Φ γ (coprod A B))
      {l r : Flat Φ labels (n + 1)} (left : Body Φ L (γ.snoc A) l) (right : Body Φ L (γ.snoc B) r) :
      Body Φ L γ (.case e.1 l r)

/-- Collect internal targets from the actual syntax, including both case arms. -/
def targets : {m : Nat} → Flat Φ (blocks + exits) m → List (Fin blocks)
  | _, .br i _ => Fin.addCases (fun j => [j]) (fun _ => []) i
  | _, .let₁ _ tail | _, .let₂ _ tail => targets tail
  | _, .case _ left right => targets left ++ targets right

def localTargets (g : FiniteCFG Φ blocks exits n) (i : Fin blocks) : List (Fin blocks) :=
  targets (g.block i)

/-- Select typed operand witnesses for the exact written table. -/
structure Witness (g : FiniteCFG Φ blocks exits n) (β : BoundCtx τ n)
    (R : Fin blocks → τ) (D : Fin exits → τ) where
  entry : Body Φ (append R D) β g.entry
  block : ∀ i, Body Φ (append R D) (β.snoc (R i)) (g.block i)

local notation "Result" => Region.packedExitType (List.ofFn D)

/-- Under a local operand binder, recover the shared context and the newest
packet for the independently expanded target. -/
def weakenPacket (s : Scope β γ) {A B : τ} (a : Operand Φ (β.snoc A) B) :
    Operand Φ (γ.snoc A) B :=
  ⟨_, a.2.rename (s.renaming.up A)⟩

/-- Use the checked external position or the selected local continuation. -/
def compileJump (i : Fin (blocks + exits)) (a : Operand Φ γ (append R D i))
    (localBranch : ∀ j (_eq : i = j.castAdd exits), Code Φ (γ.snoc (R j)) Result) :
    Code Φ γ Result :=
  Fin.addCases
    (motive := fun i => (a : Operand Φ γ (append R D i)) →
      (∀ j (_eq : i = j.castAdd exits), Code Φ (γ.snoc (R j)) Result) → Code Φ γ Result)
    (fun j a next => .join (.br ((SSA.FiniteSum.append_left R D j) ▸ a)) (next j rfl))
    (fun j a _ => .br (FiniteExit.tag (List.ofFn D) j.val (SSA.FiniteSum.at_ofFn D j)
      ((SSA.FiniteSum.append_right R D j) ▸ a))) i a localBranch

/-- Expand a body using the existing structured acyclic let/case/join grammar.
Local jumps evaluate their argument before entering a weakened continuation. -/
def compileBody : {m : Nat} → {γ : BoundCtx τ m} → {t : Flat Φ (blocks + exits) m} →
    (b : Body Φ (append R D) γ t) → Scope β γ →
    (∀ j ∈ targets t, Operand Φ (β.snoc (R j)) Result) → Code Φ γ Result
  | _, _, _, .br i a, s, next => compileJump i a (fun j eq =>
      .br (weakenPacket s (next j (by simp [targets, eq]))))
  | _, _, _, .let₁ a tail, s, next => .let₁ a (compileBody tail (.skip s _) next)
  | _, _, _, .let₂ a tail, s, next => .let₂ a (compileBody tail (.skip (.skip s _) _) next)
  | _, _, _, .case e left right, s, next => .case e
      (compileBody left (.skip s _) fun j edge => next j (List.mem_append_left _ edge))
      (compileBody right (.skip s _) fun j edge => next j (List.mem_append_right _ edge))

variable {g : FiniteCFG Φ blocks exits n}

/-- Follow the checked ranks of the written rows. Each continuation keeps the
original shared context and that row's exact incoming packet type. -/
def compileAt (w : Witness g β R D) (ranked : Rank.check (localTargets g) = true) (i : Fin blocks) :
    Code Φ (β.snoc (R i)) Result :=
  compileBody (w.block i) (.skip .base (R i))
    (fun j _edge => (compileAt w ranked j).toLetCase)
termination_by ((Rank.rounds (localTargets g) blocks).get i).getD 0
decreasing_by exact Rank.check_sound (localTargets g) ranked ‹j ∈ _›

def compile (w : Witness g β R D) (ranked : Rank.check (localTargets g) = true) :
    Code Φ β Result :=
  compileBody w.entry .base (fun j _ => (compileAt w ranked j).toLetCase)

end Silmaril.Isotope.LambdaSSA.Acyclic.FlatLetCase
