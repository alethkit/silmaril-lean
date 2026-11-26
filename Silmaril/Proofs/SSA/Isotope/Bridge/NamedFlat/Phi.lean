module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.WholeRun.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Thms
import Silmaril.Semantics.Elgot.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.LambdaSSA (FiniteCFG Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.SSA.LambdaRTL

universe u
variable {V K F α : Type u} {n : Nat} [DecidableEq V] [DecidableEq K]

omit [DecidableEq V] in
private theorem number_return (returns : Part (Option K × Value α)) (value : Value α) :
    (0, value) ∈ (returns >>= numberExit ([none] : List (Option K))) ↔ (none, value) ∈ returns := by
  rw [Part.bind_eq_bind, Part.mem_bind_iff]
  constructor
  · rintro ⟨⟨label, payload⟩, observed, numbered⟩
    cases label with
    | none =>
        change (0, value) ∈ Part.some (0, payload) at numbered
        obtain rfl : value = payload := congrArg Prod.snd (Part.mem_some_iff.mp numbered)
        exact observed
    | some _ => simp [numberExit, number] at numbered
  · intro returned
    exact ⟨(none, value), returned, Part.mem_some _⟩

theorem run_iff {source : CFG.Cyclic.Phi.Graph V K F} {lexical : CFG (Option V × Nat) (Option K) F}
    {captures : Fin n → Option V × Nat} {target : FiniteCFG F lexical.blocks.length 1 n}
    {prim : F → Value α → Part (Value α)} {input : V → Value α} {env : Env α}
    {value : Value α}
    (lowered : CFG.Cyclic.Phi.compile source = some lexical)
    (accepted : elaborate lexical [none] captures = some target)
    (inputs : ∀ i : Fin n, env i.val = CFG.Cyclic.Phi.inputEnv (model prim) input (captures i)) :
    (none, value) ∈ CFG.Cyclic.Phi.run (model prim) source input ↔
      Eval (instr prim) env target.erase () 0 value () := by
  rw [← number_return, CFG.Cyclic.Phi.run_commutes lowered (model prim) ⟨fun _ _ => rfl⟩ input]
  exact Silmaril.Isotope.Bridge.NamedFlat.run_iff accepted inputs

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi
