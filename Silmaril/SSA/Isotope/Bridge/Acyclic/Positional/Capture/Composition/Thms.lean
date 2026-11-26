module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Laws

/-! # Native category laws for written linking on literal packed inputs

Objects are nonempty ordered lists of atom-free types. Individual payload
types may be empty. The shared ambient context and primitive signature
satisfy the finite structural assumptions of the ordered trace separator.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition

open CategoryTheory
open Region (packedExitType)
open Reverse (CheckedTable checkedSetoid)
open LetCase.Structural.Finite (Context StructuralContext)
open LetCase.Structural.Reply (run)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

local notation "Val" => LetCase.Structural.Finite.Value

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : Context d} {I J K L : LCtx (Ty Empty)}

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

/-- Composition at representatives uses the literal linked table. -/
@[simp] theorem seqClass_mk (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K) :
    seqClass input (Quotient.mk _ p) (Quotient.mk _ q) = Quotient.mk _ (seq p q) := by
  simp only [seqClass, Quotient.map₂_mk]

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

/-- The checked decoder is a right identity at the literal packed endpoints. -/
theorem right_identity_replay (input : StructuralContext β) (h : J ≠ [])
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J) :
    let linked := seq p (identity h)
    ReplayEqv false (β.snoc (packedExitType I)).toList
      (linked.table.packedSSA 0 linked.entry) (p.table.packedSSA 0 p.entry) [packedExitType J] :=
  right_identity_proof input h p

/-- Sequencing the written identity after a representative preserves its class. -/
theorem right_identity (input : StructuralContext β) (h : J ≠ []) (p : Hom Φ β I J) :
    seqClass input p (Quotient.mk _ (identity h)) = p :=
  Quotient.inductionOn p fun r => by
    rw [seqClass, Quotient.map₂_mk]
    exact Quotient.sound (right_identity_replay input h r)

/-- Both written associations replay to each other at their original packed
input and ordered output. The three tables retain their own global checks. -/
theorem associative_replay (input : StructuralContext β)
    (p : CheckedTable Φ (β.snoc (packedExitType I)) J)
    (q : CheckedTable Φ (β.snoc (packedExitType J)) K)
    (r : CheckedTable Φ (β.snoc (packedExitType K)) L) :
    let left := seq (seq p q) r
    let right := seq p (seq q r)
    ReplayEqv false (β.snoc (packedExitType I)).toList
      (left.table.packedSSA 0 left.entry) (right.table.packedSSA 0 right.entry) [packedExitType L] :=
  associative_proof input p q r

/-- Written linking is associative on the native packed replay quotient. -/
theorem associative (input : StructuralContext β)
    (p : Hom Φ β I J) (q : Hom Φ β J K) (r : Hom Φ β K L) :
    seqClass input (seqClass input p q) r = seqClass input p (seqClass input q r) :=
  Quotient.inductionOn₃ p q r fun p₀ q₀ r₀ => by
    simp only [seqClass, Quotient.map₂_mk]
    exact Quotient.sound (associative_replay input p₀ q₀ r₀)

/-- The category uses the existing native packed replay classes as homs,
the written decoder as identity, and the written checked linker as composition. -/
instance (input : StructuralContext β) : Category (Interface Φ β input) where
  Hom I J := Hom Φ β I.exits J.exits
  id I := Quotient.mk _ (identity I.nonempty)
  comp p q := seqClass input p q
  id_comp p := left_identity input _ p
  comp_id p := right_identity input _ p
  assoc p q r := associative input p q r

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition
