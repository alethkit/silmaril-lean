module

public import Silmaril.SSA.PEG.Bridge.ForwardCFG.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Thms
import Silmaril.Proofs.SSA.PEG.Bridge.ForwardCFG.Correctness

public section

namespace Silmaril.SSA.PEG.Bridge.ForwardCFG

open RVSDG (Tuple)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.RVSDG.MLIR

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results ts : List (Ty Data)} {n : Nat}
variable {sigs : List (List (ValuePort Data))}

theorem inputStore_inputs (m : TotalModel P) (env : Tuple m.toPEG.Value params) :
    Inputs m env (inputStore m env) :=
  Proofs.inputStore_inputs m env

theorem cfg_blocks (g : Graph P params results n 0) (ordered : Ordered g) :
    (toCFG g ordered).blocks = [] :=
  Proofs.cfg_blocks g ordered

theorem Value.unpack_pack [DecidableEq Data] {C : Ty Data → Type} (xs : Tuple C ts) :
    (Value.pack xs).unpack ts = some xs :=
  Proofs.unpack_pack xs

variable (m : TotalModel P) [DecidableEq Data]

/-- The lexical reading of the generated λRTL region returns the ordered RVSDG
results at its single external label. -/
theorem evalSSA_fromRVSDG
    (g : RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results))
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    (fromRVSDG g).evalSSA (model m) store =
      some ((), Value.pack (fromPorts results
        (g.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env)))) :=
  Proofs.evalSSA_fromRVSDG m g env store input

/-- Mutable λRTL execution returns the same payload and preserves the store
at every argument register and every unallocated temporary. -/
theorem evalRTL_fromRVSDG
    (g : RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results))
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    ∃ final : Store m,
      (fromRVSDG g).evalRTL (model m) store = some ((), Value.pack (fromPorts results
        (g.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))), final) ∧
      ∀ reg, ReadOnly sigs.length reg → final reg = store reg :=
  Proofs.evalRTL_fromRVSDG m g env store input

/-- Flattening keeps the payload and the store frame, and embeds the exit as
an external CFG label. -/
theorem cfg_run (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    ∃ final : Store m,
      (toCFG g ordered).run (model m) store = some (Sum.inl (), Value.pack (fromPorts results
        ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))), final) ∧
      ∀ reg, ReadOnly (translate g ordered).1.length reg → final reg = store reg :=
  Proofs.cfg_run m g ordered env store input

theorem observeCFG_rvsdg (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    observeCFG g ordered m store = some (Sum.inl (), fromPorts results
      ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))) :=
  Proofs.observeCFG_rvsdg m g ordered env store input

/-- At the external return label, the decoded slots agree with the actual
guarded Figure 11 observation. -/
theorem observeCFG_peg (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store)
    (idx : Index 0) (wf : WellFounded g.Demand) :
    (observeCFG g ordered m store).map (fun e => (e.1, e.2.map (fun _ => some))) =
      some (Sum.inl (), g.observe m.toPEG (g.denote m.toPEG env wf) idx) :=
  Proofs.observeCFG_peg m g ordered env store input idx wf

/-- Read back the same ordered values as the checked regionless MLIR block in
the induced model. -/
theorem observeCFG_mlir (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    observeCFG g ordered m store =
      some (Sum.inl (), fromPorts results (Regionless.ofAssignment (F := m.toRVSDG.Val) results (fun i =>
        (translateMLIR g ordered i).denote m.toMLIR
          (Regionless.toAssignment params (toPorts (F := m.toRVSDG.Val) env))))) :=
  Proofs.observeCFG_mlir m g ordered env store input

end Silmaril.SSA.PEG.Bridge.ForwardCFG
