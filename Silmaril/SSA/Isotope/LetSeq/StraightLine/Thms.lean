module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Reflection
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Separation

/-! # Trace reflection for native open LetSeq terms -/

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)

/-- Replay uses native `bindPair`, pure let β and congruence. -/
theorem Admitted.replay {n : Nat} {β : BoundCtx Types n} {t : Term n}
    (p : Admitted β t) : Equiv false Γ₀ β t p.normal Atom :=
  replay_proof p

/-- Run one request, then bind the two reply coordinates in native order. -/
theorem run_request {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
    (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body)
    (ρ : BoundEnv Value β) :
    run (canonicalDerivation (.request f x y rest)) ρ =
      model.eval f (x.value ρ, y.value ρ) >>= fun ab =>
        run (canonicalDerivation rest) ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) :=
  run_request_proof f x y rest ρ

theorem mem_request_trace {A : Type} {f : Request} {arg : Nat × Nat} {k : Nat × Nat → Trace A}
    {z : A} {w : Log} :
    (z, w) ∈ (model.eval f arg >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, arg, reply⟩ * tail = w :=
  request_mem_proof

/-- A separating environment suffices. Fresh reply coordinates chosen in
one legal trace then separate all retained input and reply projections. -/
theorem run_eq_iff_normal {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    run d ρ = run e ρ ↔ p.normal = q.normal :=
  run_eq_iff_normal_proof p q d e ρ fresh sep

theorem native_iff_normal {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    Equiv false Γ₀ β t u Atom ↔ p.normal = q.normal :=
  native_iff_normal_proof p q d e ρ fresh sep

/-- The existing typed embedding preserves and reflects native equations on
the admitted slice with a separating input environment. -/
theorem embed_iff_native {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Admitted β t) (q : Admitted β u)
    (d : Derivation Request Γ₀ β t Atom) (e : Derivation Request Γ₀ β u Atom)
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    LetCase.LocallyNameless.Equiv false Γ₀ β (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) Atom ↔
      Equiv false Γ₀ β t u Atom :=
  embed_iff_native_proof p q d e ρ fresh sep

theorem entry_run {body : Term 3}
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) body Atom) (x y : Nat) :
    run (entry d) (packetEnv (x, y)) =
      run d (((packetEnv (x, y)).snoc (A := Atom) x).snoc (A := Atom) y) :=
  entry_run_proof d x y

theorem entry_run_eq_iff_normal {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔ p.normal = q.normal :=
  entry_iff_normal_proof p q d e

/-- The concrete point `(0, 1)` separates the actual open packet terms. -/
theorem entry_run_eq_iff_native {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    run (entry d) (packetEnv (0, 1)) = run (entry e) (packetEnv (0, 1)) ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom :=
  entry_iff_native_proof p q d e

/-- Native LetCase equivalence of the actual embedded packet terms is
equivalent to native LetSeq equivalence. -/
theorem entry_embed_iff_native {t u : Term 3}
    (p : Admitted ((input.snoc Atom).snoc Atom) t)
    (q : Admitted ((input.snoc Atom).snoc Atom) u)
    (d : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) t Atom)
    (e : Derivation Request Γ₀ ((input.snoc Atom).snoc Atom) u Atom) :
    LetCase.LocallyNameless.Equiv false Γ₀ input
      (Morphism.SeqCase.embed (.let₂ (.bv 0) t)) (Morphism.SeqCase.embed (.let₂ (.bv 0) u)) Atom ↔
      Equiv false Γ₀ input (.let₂ (.bv 0) t) (.let₂ (.bv 0) u) Atom :=
  entry_embed_iff_native_proof p q d e

end Silmaril.Isotope.LetSeq.StraightLine
