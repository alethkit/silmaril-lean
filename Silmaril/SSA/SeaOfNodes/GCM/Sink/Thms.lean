module

public import Silmaril.SSA.SeaOfNodes.GCM.Sink.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.Correctness

/-! # Typing and finite returns for the single-arm sink -/

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.Sink

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

universe u v w x

variable {Φ : Type u} {τ : Type v} {α : Type w} {σ : Type x}

theorem before_hasType [TypeFormers τ] [HasTy Φ τ] (op : Φ) :
    (before op).HasType (inputs (τ := τ) op) [instrTrg op] :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.before_hasType op

theorem after_hasType [TypeFormers τ] [HasTy Φ τ] (op : Φ) :
    (after op).HasType (inputs (τ := τ) op) [instrTrg op] :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.after_hasType op

/-- The matcher certifies the full input shape and the emitted CFG. -/
theorem sink?_shape {r r' : Region Φ} :
    sink? r = some r' ↔ ∃ op, r = before op ∧ r' = after op :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.sink?_shape

/-- Under the pure total model, the sunk CFG has exactly the specified
result and returns at exit zero with the input state. -/
theorem after_eval_iff (compute : Φ → Value α → Value α) (op : Φ)
    (env : Env α) (start finish : σ) (label : Nat) (value : Value α) :
    Eval (instruction compute) env (after op) start label value finish ↔
      label = 0 ∧ result? compute op env = some value ∧ finish = start :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.after_eval_iff compute op env start finish label value

/-- Every successful rewrite preserves and reflects the actual λSSA finite
return relation for every entry environment and ambient state. -/
theorem sink?_eval_iff {r r' : Region Φ} (changed : sink? r = some r')
    (compute : Φ → Value α → Value α) (env : Env α) (start finish : σ) (label : Nat)
    (value : Value α) :
    Eval (instruction compute) env r start label value finish ↔
      Eval (instruction compute) env r' start label value finish :=
  Silmaril.Proofs.SSA.SeaOfNodes.GCM.Sink.sink?_eval_iff changed compute env start finish label value

end Silmaril.SSA.SeaOfNodes.GCM.Sink
