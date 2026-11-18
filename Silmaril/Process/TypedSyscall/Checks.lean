module

import Silmaril.Process.Syscall
import Silmaril.Process.TypedSyscall.Thms

/-! A small client signature and the existing Linux write/exit relation. The client
sees a count or failure, but cannot inspect the errno or resume after exit. -/

namespace Silmaril.Process.TypedSyscall

private inductive ClientRequest where
  | send (address count : Nat)
  | exit (status : Nat)

private def client : Signature := ⟨ClientRequest, fun
  | .send .. => Option Nat
  | .exit _ => Empty⟩

private def linux : Signature := ⟨Syscall.Request, fun
  | .read .. | .write .. => Syscall.Result
  | .exit _ => Empty⟩

private def request : ClientRequest → Syscall.Request
  | .send address count => .write 1 address count
  | .exit status => .exit status

private def toLinux : client.Hom linux where
  request := request
  response req reply := match req with
    | .send .. => match reply with | .ok count => some count | .error _ => none
    | .exit _ => reply

private def wireResult : (req : linux.Request) → linux.Response req → Syscall.Result
  | .read .., reply | .write .., reply => reply
  | .exit _, impossible => nomatch impossible

private def linuxKernel : Kernel linux Syscall.State Syscall.Event := fun req before event answer =>
  match answer with
  | .returned reply after => Syscall.Step before req event (.returned (wireResult req reply)) after
  | .exited status after => Syscall.Step before req event (.exited status) after

private structure Buffer where
  address : Nat
  count : Nat

private inductive Stage where
  | ready
  | sent (count : Option Nat)

private def cpu : Cpu client Buffer Stage Syscall.State Empty := fun image stage _ =>
  match stage with
  | .ready => .call (.send image.address image.count) Stage.sent
  | .sent count => .call (.exit (if count = some 1 then 0 else 1)) (fun impossible => nomatch impossible)

private def buffer : Buffer := ⟨0x1000, 1⟩
private def memory : Memory :=
  ⟨[⟨0x1000, 1, ⟨true, false, false⟩⟩], Memory.install ∅ 0x1000 [0x41]⟩
private def stdout : Syscall.Descriptor := ⟨false, true, .ofList [], 0, []⟩
private def initial : Syscall.State := ⟨memory, fun fd => if fd = 1 then some stdout else none, none⟩
private def written := initial.setDescriptor 1 { stdout with output := [0x41] }

example : Step cpu (linuxKernel.pull toLinux) (Scheduler.single Stage) buffer .ready initial
    (some (.write 1 [0x41])) (.running (.sent (some 1)) written) := by
  apply (step_push_iff toLinux cpu linuxKernel ..).mp
  refine ⟨.write 1 [0x41], .returned (.ok 1) written, ?_, rfl, rfl⟩
  have loaded : memory.readBytes 0x1000 1 = some [0x41] :=
    Memory.readWith_eq memory .read 0x1000 [0x41] (by decide) (Memory.install_get _ _ _)
  exact Syscall.Step.writeSome (state := initial) (fd := 1) (address := 0x1000) (count := 1)
    (written := 1) (descriptor := stdout) rfl rfl rfl loaded (by decide) (by decide)

example : Step cpu (linuxKernel.pull toLinux) (Scheduler.single Stage) buffer (.sent (some 1)) written
    (some (.exit 0)) (.exited 0 { written with exited := some 0 }) := by
  apply (step_push_iff toLinux cpu linuxKernel ..).mp
  exact ⟨.exit 0, .exited 0 _, Syscall.Step.exit 0 rfl, rfl, rfl⟩

private def closed : Syscall.State := { initial with descriptors := fun _ => none }

example : Step cpu (linuxKernel.pull toLinux) (Scheduler.single Stage) buffer .ready closed
    (some (.error (.write 1 0x1000 1) .badDescriptor)) (.running (.sent none) closed) := by
  apply (step_push_iff toLinux cpu linuxKernel ..).mp
  exact ⟨_, .returned (.error .badDescriptor) closed,
    Syscall.Step.writeBadDescriptor rfl (by decide), rfl, rfl⟩

example : Step cpu (linuxKernel.pull toLinux) (fun (_ : Stage) => none) buffer .ready initial none .idle :=
  ⟨rfl, rfl⟩

#print axioms step_push_iff
#print axioms Kernel.pull_then

end Silmaril.Process.TypedSyscall
