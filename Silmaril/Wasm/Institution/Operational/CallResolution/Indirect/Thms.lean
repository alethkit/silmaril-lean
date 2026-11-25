module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Rules

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open CallContinuation.OuterCall.Ranked.Graph (Program Function)
open Execution.Runtime (Frame Value)

theorem resolve_iff {site : Site} {program : Program} {selector : BitVec 32} {out : Outcome} :
    site.resolve program selector = some out ↔ Resolution site program selector out :=
  Proofs.resolve_iff

theorem resolve_total {site : Site} {program : Program} {caller : Frame} {selector : BitVec 32}
    (checked : site.check program caller = true) : ∃ out, site.resolve program selector = some out :=
  Proofs.resolve_total checked

theorem resolved_signature {site : Site} {program : Program} {selector : BitVec 32}
    {addr : Execution.Runtime.FuncAddr} {fn : Function}
    (resolved : site.resolve program selector = some (.resolved addr))
    (found : program.lookup addr = some fn) : fn.declaration.type = site.signature := by
  cases resolve_iff.mp resolved with
  | resolved _ lookup same => exact Option.some.inj (lookup.symm.trans found) ▸ same

theorem resolved_frame_entry {site : Site} {program : Program} {selector : BitVec 32}
    {addr : Execution.Runtime.FuncAddr} {fn : Function} {args : List Value}
    (resolved : site.resolve program selector = some (.resolved addr))
    (found : program.lookup addr = some fn) (typed : args.map Value.type = site.signature.params) :
    program.FrameEdge addr (.invoke args) (.label (fn.declaration.frame args).locals (.running fn.initial fn.code)) :=
  (program.frameEdge_iff found).mpr (.enter args (by
    simpa [← resolved_signature resolved found, CallContinuation.OuterCall.Declaration.type] using typed))

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
