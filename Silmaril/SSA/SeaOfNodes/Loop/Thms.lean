module

public import Silmaril.SSA.SeaOfNodes.Loop.Denotation
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.Correctness

/-! # Source execution, bounded evaluation and finite denotation -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop

open Diamond (Model Signature Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Port Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out : ValueSort Data}
variable (g : Graph Op inputs carried entrySigs headerSigs out) (m : Model.{u, v, w} Op)

/-- Each new Phi reads its own operand from the same predecessor snapshot. -/
theorem Graph.latch_get (edge : Incoming)
    (args : Tuple (Val m.value) (edge.select (dataPorts inputs) (headerPorts inputs carried)))
    (locals : Locals (Val m.value) (extend [] (edge.select entrySigs headerSigs)))
    {t : Ty Data} (port : Port (dataPorts carried) t) :
    (g.latch m edge args locals).get port =
      Diamond.read m ((g.phiInputs edge).get port) args locals :=
  Proofs.latch_get g m edge args locals port

variable (input : Tuple (Val m.value) (dataPorts inputs)) (result : sortValue m.value out)

/-- A finite run with at most the given number of backedges is exactly a
successful observation of the bounded evaluator. -/
theorem Graph.evalBackedges_eq_some_iff (budget : Nat) :
    g.evalBackedges m budget input = some result ↔
      ∃ count ≤ budget, g.ReturnsAfter m input count (g.initial m input) result :=
  Proofs.evalBackedges_eq_some_iff g m budget input result

/-- Every finite return is found with sufficient budget. -/
theorem Graph.returns_iff_evalBackedges :
    g.Returns m input result ↔ ∃ budget, g.evalBackedges m budget input = some result :=
  Proofs.returns_iff_evalBackedges g m input result

/-- The partial denotation preserves and reflects finite returns. -/
theorem Graph.returns_iff_mem_denote :
    g.Returns m input result ↔ result ∈ g.denote m input :=
  Proofs.returns_iff_mem_denote g m input result

/-- An invariant that forces another backedge excludes every finite return. -/
theorem Graph.not_returns_of_backedge_invariant
    (invariant : Tuple (Val m.value) (dataPorts carried) → Prop)
    (initial : invariant (g.initial m input))
    (continues : ∀ old, invariant old → ∃ next, g.step m input old = .inr next ∧ invariant next) :
    ¬ g.Returns m input result :=
  Proofs.not_returns_of_backedge_invariant invariant initial continues

end Silmaril.SSA.SeaOfNodes.Loop
