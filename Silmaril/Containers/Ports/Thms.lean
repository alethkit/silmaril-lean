module

public import Silmaril.Containers.Ports.Defs
import Silmaril.Proofs.Containers.Ports.Basic

/-!
# Published ports: theorems

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

PROVED (standard axioms). `publish_nil`: with no published port the table is LPS's native table,
so the extension leaves the base model unchanged. `publish_of_not`: off a bind to a published
port it is LPS's table. `publish_of_published`: on one, it is LPS's `bindSpec` with the port read
as 0.
-/

public section

namespace Silmaril.Containers.Ports

open Silmaril.Process.LPS

theorem publish_nil : publish [] = Probes.spec := Silmaril.Proofs.Containers.Ports.publish_nil

theorem publish_of_not {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = false)
    (m : Silmaril.Process.LPS.Model) (o : Silmaril.Process.LPS.Outcome SyscallEffect) : publish ports i m o ↔ Probes.spec i m o :=
  Silmaril.Proofs.Containers.Ports.publish_of_not h m o

theorem publish_of_published {ports : List Nat} {i : SyscallInput} (h : publishedBind ports i = true)
    (m : Silmaril.Process.LPS.Model) (o : Silmaril.Process.LPS.Outcome SyscallEffect) :
    publish ports i m o ↔ bindSpec (fd32 (i.arg 0)) (i.arg 1) (i.arg 2) (zeroPort i (i.arg 1)) m o :=
  Silmaril.Proofs.Containers.Ports.publish_of_published h m o

end Silmaril.Containers.Ports
