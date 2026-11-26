module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold.Correctness

/-! Feedback materialization preserves native observations on covered inputs. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact TupleCovers)
open RVSDG (Port Tuple)
open ReturnFold (Literals)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)}
variable {entrySigs headerSigs : List (List (Ty Data))} {out sort : ValueSort Data}
variable {m : Model.{u, v, w} Op} [BankDecidableEq m.value (dataPorts carried)]
variable {g : Graph Op inputs carried entrySigs headerSigs out}
variable {input : Tuple (Fact m.value) (dataPorts inputs)} {literals : Literals m sort}
variable {port : Port (dataPorts carried) (.value sort)}
variable {rewritten : Graph Op inputs carried entrySigs (headerSigs ++ [[.value sort]]) out}
variable {entry : Tuple (Val m.value) (dataPorts inputs)}

theorem rewrite_ok_iff :
    rewrite m g input port literals = .ok rewritten ↔
      ∃ value, feedbackFact m g input port = .constant value ∧
        rewritten = withLiteral g port (literals.opcode value) :=
  Proofs.rewrite_ok_iff

/-- The native step agrees at each activation reached in the original graph.
In particular every taken backedge delivers the same full latch tuple. -/
theorem step_eq (success : rewrite m g input port literals = .ok rewritten) (covered : TupleCovers input entry)
    {via : Incoming} {count : Nat} {old : Tuple (Val m.value) (dataPorts carried)}
    (arrived : Arrives m g entry via count old) :
    rewritten.step m entry old = g.step m entry old :=
  Proofs.step_eq success covered arrived

theorem evalBackedges_eq (success : rewrite m g input port literals = .ok rewritten)
    (covered : TupleCovers input entry) (budget : Nat) :
    rewritten.evalBackedges m budget entry = g.evalBackedges m budget entry :=
  Proofs.evalBackedges_eq success covered budget

theorem returns_iff (success : rewrite m g input port literals = .ok rewritten)
    (covered : TupleCovers input entry) (result : sortValue m.value out) :
    rewritten.Returns m entry result ↔ g.Returns m entry result := by
  simp only [Graph.returns_iff_evalBackedges, evalBackedges_eq success covered]

theorem noFiniteReturn_iff (success : rewrite m g input port literals = .ok rewritten)
    (covered : TupleCovers input entry) :
    (¬ ∃ result, rewritten.Returns m entry result) ↔ ¬ ∃ result, g.Returns m entry result := by
  simp only [returns_iff success covered]

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.FeedbackFold
