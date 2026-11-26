module

public import Silmaril.SSA.Isotope.Institution.Thms
public import Silmaril.Semantics.NondeterministicTrace.Thms
public import Mathlib.Algebra.FreeMonoid.Basic

/-! # Native LetSeq terms with ordered pair requests and atomic projections -/

@[expose] public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Isotope.Semantics (BoundEnv InstructionModel)
open Silmaril.Semantics.NondeterministicTrace

abbrev Types := Ty Unit
abbrev Atom : Types := .base ()
abbrev Packet : Types := .product Atom Atom

/-- Distinct requests with a common pair interface. -/
inductive Request where
  | ask (label : Bool)

instance : HasTy Request Types := ⟨fun _ => Packet, fun _ => Packet⟩
instance : HasEff Request Bool := ⟨fun _ => true⟩

abbrev Term := Tm Empty Request
abbrev Γ₀ : Ctx Empty Types := .nil

abbrev Value := Ty.denote (fun _ : Unit => Nat)

/-- A recorded request includes its actual argument and reply coordinates. -/
structure Event where
  request : Request
  argument : Nat × Nat
  reply : Nat × Nat

abbrev Log := FreeMonoid Event
abbrev Trace := Silmaril.Semantics.NondeterministicTrace.Finite Log

def model : InstructionModel Value Request Trace where
  eval f x := Finite.ofOutcomes (Set.range fun y : Nat × Nat => (y, FreeMonoid.of ⟨f, x, y⟩))

def run {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (d : Derivation Request Γ₀ β t A) (ρ : BoundEnv Value β) : Trace (Value A) :=
  d.denote Value model (fun x => x.elim) ρ

/-- A retained variable at the atomic sort, possibly below a packet binder. -/
abbrev Slot {n : Nat} (β : BoundCtx Types n) := {i : Fin n // β.get i = Atom}

def Slot.value {n : Nat} {β : BoundCtx Types n} (s : Slot β) (ρ : BoundEnv Value β) : Nat :=
  cast (congrArg Value s.2) (ρ s.1)

def requestTerm {n : Nat} (f : Request) (x y : Fin n) : Term n :=
  .op f (.pair (.bv x) (.bv y))

/-- Native straight-line terms. Each request binds the left reply then
the right reply. A packet binder may precede destructuring, and an atomic
return may use an explicit pure alias. -/
inductive Admitted : {n : Nat} → (β : BoundCtx Types n) → Term n → Type where
  | ret {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Admitted β (.bv x.1)
  | aliasReturn {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Admitted β (.let₁ (.bv x.1) (.bv 0))
  | request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Admitted ((β.snoc Atom).snoc Atom) body) :
      Admitted β (.let₂ (requestTerm f x.1 y.1) body)
  | bound {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Admitted ((β.snoc Atom).snoc Atom) body) :
      Admitted β (.let₁ (requestTerm f x.1 y.1) (.let₂ (.bv 0) body.underTwoBinders))

/-- The normal forms are native terms with direct packet destructuring and
direct variable returns. -/
inductive Canonical : {n : Nat} → (β : BoundCtx Types n) → Term n → Type where
  | ret {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
      Canonical β (.bv x.1)
  | request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
      (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body) :
      Canonical β (.let₂ (requestTerm f x.1 y.1) body)

def Admitted.normal {n : Nat} {β : BoundCtx Types n} {t : Term n} :
    Admitted β t → Term n
  | .ret x | .aliasReturn x => .bv x.1
  | .request f x y rest | .bound f x y rest =>
    .let₂ (requestTerm f x.1 y.1) rest.normal

def slotDerivation {n : Nat} {β : BoundCtx Types n} (x : Slot β) :
    Derivation Request Γ₀ β (.bv x.1) Atom :=
  cast (congrArg (Derivation Request Γ₀ β (.bv x.1)) x.2) .bv

def requestDerivation {n : Nat} {β : BoundCtx Types n} (f : Request) (x y : Slot β) :
    Derivation Request Γ₀ β (requestTerm f x.1 y.1) Packet :=
  .op (.pair (slotDerivation x) (slotDerivation y))

def canonicalDerivation {n : Nat} {β : BoundCtx Types n} {t : Term n} :
    Canonical β t → Derivation Request Γ₀ β t Atom
  | .ret i => slotDerivation i
  | .request f x y rest => .let₂ (requestDerivation f x y) (canonicalDerivation rest)

def normalWitness {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (w : Admitted β t) : Canonical β w.normal :=
  match w with
  | .ret i | .aliasReturn i => .ret i
  | .request f x y rest | .bound f x y rest => .request f x y (normalWitness rest)

/-- The atom slots carry distinct atoms below a supply for fresh replies. -/
structure Separating {n : Nat} {β : BoundCtx Types n} (ρ : BoundEnv Value β) (fresh : Nat) : Prop where
  injective : Function.Injective (fun s : Slot β => s.value ρ)
  below : ∀ s : Slot β, s.value ρ < fresh

/-- Every input supplied to the open packet program is a native product. -/
abbrev input : BoundCtx Types 1 := .snoc .nil Packet

def packetEnv (pair : Nat × Nat) : BoundEnv Value input :=
  BoundEnv.snoc (β := .nil) (A := Packet) (fun i => i.elim0) pair

/-- The entry explicitly projects the two components of that native input. -/
def entry {body : Term 3}
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) body Atom) :
    Derivation Request Γ₀ input (.let₂ (.bv 0) body) Atom :=
  .let₂ .bv d

end Silmaril.Isotope.LetSeq.StraightLine
