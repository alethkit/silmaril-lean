module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.GuardFold.Correctness

/-! The guard rewrite preserves every reached native step. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Tuple)
open ReturnFold (Literals Refusal)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)} {literals : Literals m .predicate}
variable {rewritten : Graph Op inputs carried entrySigs (headerSigs ++ [[.value .predicate]]) out}
variable {entry : Tuple (Val m.value) (dataPorts inputs)}

theorem rewrite_ok_iff :
    rewrite m g input literals = .ok rewritten ↔
      ∃ test : Bool, guardFact m g input = .constant ⟨test⟩ ∧
        rewritten = withLiteral g (literals.opcode ⟨test⟩) :=
  Proofs.rewrite_ok_iff

theorem rewrite_error_iff (reason : Refusal) :
    rewrite m g input literals = .error reason ↔
      match reason with
      | .unseen => guardFact m g input = .bottom
      | .overdefined => guardFact m g input = .overdefined :=
  Proofs.rewrite_error_iff reason

/-- In the fixed point, the guard fact determines every mark after entry. -/
theorem executable_eq :
    (SCCP.solve m g input).1 = insert (incomingIndex .entry) (successors (guardFact m g input)) :=
  Proofs.executable_eq

/-- The rewrite selects the same successor and delivers its full payload at
each activation reached in the original graph. -/
theorem step_eq (success : rewrite m g input literals = .ok rewritten) (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    rewritten.step m entry old = g.step m entry old :=
  Proofs.step_eq success covered arrived

theorem evalBackedges_eq (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry :=
  Proofs.evalBackedges_eq success covered budget

theorem returns_iff (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) (result : sortValue m.value out) :
    rewritten.Returns m entry result ↔ g.Returns m entry result := by
  simp only [Graph.returns_iff_evalBackedges, evalBackedges_eq success covered]

theorem noFiniteReturn_iff (success : rewrite m g input literals = .ok rewritten)
    (covered : TupleCovers input entry) :
    (¬ ∃ result, rewritten.Returns m entry result) ↔ ¬ ∃ result, g.Returns m entry result := by
  simp only [returns_iff success covered]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.GuardFold
