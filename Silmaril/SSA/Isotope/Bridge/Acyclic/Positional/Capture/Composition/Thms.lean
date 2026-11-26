module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Laws

/-! # Native left identity for written linking on literal packed inputs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition

open Region (packedExitType)
open Reverse (CheckedTable checkedSetoid)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (run)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetCase.Structural.Finite.Value

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : Context d} {I J K : LCtx (Ty Empty)}

/-- The actual linked CFG computes each stage once at the original
ambient and input packet interface. -/
theorem seq_run (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (env : BoundEnv Val β) (x : Val (packedExitType I)) :
    run (seq p q).toLetCase.2 (env.snoc x) =
      (run p.toLetCase.2 (env.snoc x) >>= fun y => run q.toLetCase.2 (env.snoc y)) :=
  seq_run_proof p q env x

/-- Changing either representative by native packed replay preserves the
native equation class of the written link. -/
theorem seq_congr (input : StructuralContext β)
    {p₁ p₂ : CheckedTable Φ (β.snoc (packedExitType I)) J}
    {q₁ q₂ : CheckedTable Φ (β.snoc (packedExitType J)) K}
    (hp : (checkedSetoid Φ (β.snoc (packedExitType I)) J).r p₁ p₂)
    (hq : (checkedSetoid Φ (β.snoc (packedExitType J)) K).r q₁ q₂) :
    (checkedSetoid Φ (β.snoc (packedExitType I)) K).r (seq p₁ q₁) (seq p₂ q₂) :=
  seq_congr_proof input hp hq

/-- Composition of native packed equation classes is induced by the written linker. -/
def seqClass (input : StructuralContext β) : Hom Φ β I J → Hom Φ β J K → Hom Φ β I K :=
  Quotient.map₂ seq (fun {_ _} hp {_ _} hq => seq_congr input hp hq)

/-- The checked decoder is a left identity by native replay at the literal
packed endpoints of the linked and original written graphs. -/
theorem left_identity_replay (input : StructuralContext β) (h : I ≠ [])
    (q : CheckedTable Φ (β.snoc (packedExitType I)) K) :
    let linked := seq (identity h) q
    ReplayEqv false (β.snoc (packedExitType I)).toList
      (linked.table.packedSSA 0 linked.entry) (q.table.packedSSA 0 q.entry) [packedExitType K] :=
  left_identity_proof input h q

/-- On the native classes, sequencing the written identity before any
representative preserves the class. -/
theorem left_identity (input : StructuralContext β) (h : I ≠ []) (q : Hom Φ β I K) :
    seqClass input (Quotient.mk _ (identity h)) q = q :=
  Quotient.inductionOn q fun r => by
    rw [seqClass, Quotient.map₂_mk]
    exact Quotient.sound (left_identity_replay input h r)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition
