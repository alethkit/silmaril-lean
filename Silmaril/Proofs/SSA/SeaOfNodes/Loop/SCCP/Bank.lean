module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs
public import Silmaril.Semantics.Dataflow.Flat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs

open Diamond (Ty Val)
open Diamond.SCCP (Fact TupleCovers TupleLE tupleFacts)
open RVSDG (Port Tuple)
open Semantics.Dataflow (Flat)

variable {Data : Type*} {value : Data → Type*} {ports : List (Ty Data)}

theorem bankTuple_tupleFacts (facts : Tuple (Fact value) ports) :
    bankTuple (tupleFacts facts) = facts := by
  induction facts with
  | nil => rfl
  | cons fact rest ih =>
    change Tuple.cons fact (bankTuple (tupleFacts rest)) = .cons fact rest
    rw [ih]

theorem tupleFacts_mono {lhs rhs : Tuple (Fact value) ports} (le : TupleLE lhs rhs) :
    tupleFacts lhs ≤ tupleFacts rhs := by
  induction lhs with
  | nil => exact fun i => i.elim0
  | cons fact rest ih =>
    cases rhs with
    | cons other tail =>
      exact fun i => Fin.cases (motive := fun j =>
        tupleFacts (.cons fact rest) j ≤ tupleFacts (.cons other tail) j)
        (le .head) (fun j => ih (fun p => le (.tail p)) j) i

theorem bankTuple_mono {lhs rhs : BankFacts value ports} (le : lhs ≤ rhs) :
    TupleLE (bankTuple lhs) (bankTuple rhs) := by
  intro t port
  induction port with
  | head => exact le 0
  | tail _ ih => exact ih fun j => le j.succ

theorem bankCovers_of_tuple {facts : Tuple (Fact value) ports} {concrete : Tuple (Val value) ports}
    (covered : TupleCovers facts concrete) : BankCovers (tupleFacts facts) concrete := by
  unfold BankCovers
  rwa [bankTuple_tupleFacts]

theorem bankCovers_mono {lhs rhs : BankFacts value ports} {concrete : Tuple (Val value) ports}
    (le : lhs ≤ rhs) (cover : BankCovers lhs concrete) : BankCovers rhs concrete :=
  fun p => Flat.covers_mono (bankTuple_mono le p) (cover p)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Proofs
