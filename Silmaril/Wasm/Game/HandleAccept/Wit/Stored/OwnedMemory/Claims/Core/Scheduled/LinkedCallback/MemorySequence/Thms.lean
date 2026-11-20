module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Machine
open Stored.Endpoints.RecordLower PayloadPrefix

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)}

/-- Traverse both actual memory sequences. Record/tuple reads are taken in
the reached store and element slots keep their validated stride. The rule
for the next sibling applies only on the preceding child's common return. -/
theorem sequence_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (compare : FieldComparison grow sig) (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    (slots : mode.Slots destination.width (FieldRule compare older origin destination inst) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst compare checkNext canonNext finish items index cursor left right check canon :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.replay
    mode destination inst items index cursor compare checkNext canonNext finish frame growth present slots ends checkAt canonAt

/-- Instantiate the traversal with actual allocating strings and live handles
in placed slots. Bounds transfer by reached Core growth, not byte stability. -/
theorem mixed_replay {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)} {origin : CStore (core3 grow)}
    (mode : Track) (destination : RecordDestination) (inst : InstId) (items : List Field) (index cursor : Nat)
    (checkNext : CheckNext grow sig) (canonNext : CanonNext grow sig) (finish : Finish grow sig)
    {left right : State grow sig} {check canon : Cursor (E := core3 grow) (HostState sig)}
    (frame : ChildFrameOver older left right check canon) (growth : Core3.Grows origin.core left.store.core)
    (present : (core3 grow).memAddrType? origin.core destination.memory = some destination.width)
    {bytes : Nat} (sized : (core3 grow).memSize? origin.core destination.memory = some bytes)
    {addr : Nat} (realloc : destination.realloc = some addr)
    (slots : mode.Slots destination.width (MixedSlot destination bytes) items cursor)
    (ends : ∀ reached reference check canon, ChildFrameOver older reached reference check canon →
      Core3.Grows origin.core reached.store.core → reached.ctl = check.control (checkNext (.ok ())) →
      reference.ctl = canon.control (canonNext ()) → finish reached reference check canon)
    (checkAt : left.ctl = check.control (mode.checked destination inst items index cursor >>= checkNext))
    (canonAt : right.ctl = canon.control (mode.canonical destination inst items cursor >>= canonNext)) :
    Replay profile ready bindings mode destination inst (mixed profile ready bindings older destination inst)
      checkNext canonNext finish items index cursor left right check canon :=
  sequence_replay mode destination inst items index cursor _ checkNext canonNext finish frame growth present
    (Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.slotsMap mode destination.width
      (fun item address slot => Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.MemorySequence.mixedRule
        destination inst item address present sized realloc slot) items cursor slots) ends checkAt canonAt

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.LinkedCallback.MemorySequence
