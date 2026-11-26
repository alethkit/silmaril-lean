module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Infinite.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Infinite.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi

open Silmaril.Isotope Silmaril.SSA.LambdaRTL
open Silmaril.Isotope.Bridge.NamedFlat (InfiniteRun model)

universe u
variable {V K F α : Type u} [DecidableEq V] [DecidableEq K]

theorem lexical_infinite_run_iff {source : CFG.Cyclic.Phi.Graph V K F}
    {lexical : CFG (Option V × Nat) (Option K) F} {prim : F → Value α → Part (Value α)}
    {input : V → Value α} (lowered : CFG.Cyclic.Phi.compile source = some lexical) :
    CFG.Cyclic.Phi.InfiniteRun (model prim) source input ↔
      InfiniteRun prim lexical (CFG.Cyclic.Phi.inputEnv (model prim) input) := by
  let encode := CFG.Cyclic.Phi.encode (model prim) source
  have entry := CFG.Cyclic.Phi.entry_mem_iff lowered (model prim) ⟨fun _ _ => rfl⟩ input
  have step := CFG.Cyclic.Phi.continue_mem_iff lowered (model prim) ⟨fun _ _ => rfl⟩ input
  constructor
  · rintro ⟨path, entered, steps⟩
    exact ⟨encode ∘ path, (entry _).mpr ⟨_, entered, rfl⟩,
      fun i => (step _ _).mpr ⟨_, steps i, rfl⟩⟩
  · rintro ⟨path, entered, steps⟩
    let Position (i : Nat) := {p : CFG.Cyclic.Phi.Pending V K (Value α) // encode p = path i}
    obtain ⟨initial, initialEntry, initialMatch⟩ := (entry _).mp entered
    have next (i : Nat) (current : Position i) :
        ∃ successor : Position (i + 1),
          Sum.inr successor.val ∈ CFG.Cyclic.Phi.step (model prim) source current.val := by
      have continued := steps i
      rw [← current.property] at continued
      obtain ⟨successor, stepped, matched⟩ := (step _ _).mp continued
      exact ⟨⟨successor, matched⟩, stepped⟩
    let lifted : (i : Nat) → Position i :=
      Nat.rec ⟨initial, initialMatch⟩ fun i p => Classical.choose (next i p)
    exact ⟨fun i => (lifted i).val, initialEntry, fun i => Classical.choose_spec (next i (lifted i))⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi
