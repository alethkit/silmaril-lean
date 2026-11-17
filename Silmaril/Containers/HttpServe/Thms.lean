module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.HttpOnce.Thms
import Silmaril.Proofs.Containers.HttpServe.Basic

/-!
# A self-contained HTTP server: theorems

> **Experimental API.** Names and statements in `Silmaril.Containers` may change.

PROVED (standard axioms; kernel evaluation for the digests, the archive, the JSON documents and
the ELF parse). Proofs are in `Silmaril.Proofs.Containers.HttpServe`.

* **The artifact.** `elf_digest` … `layer_encode`: the pinned digests; `loadElf_elf`: LPS's x86-64
  loader accepts the octets; `runtime_load`: the OCI reader, the entry-point shape and the loader
  give the program; `declared`: the configuration declares `8080/tcp`, the port of
  `Http.Fixtures.httpIface`; `addr_in_image`, `response_in_image`: the address the program binds
  and the octets it sends are in the loaded image.
* **The session, read by the server platform.** `sessionOk_sent`: in a successful session the
  connection's sent octets, read through `Http.sockTrace` and `Servers.Platform.sent` (the
  observation of `Http.platform`), are exactly `Fixtures.okResponse`; `sessionOk_exact`: so they
  are one HTTP/1.1 response, judged exactly (`HttpOnce.IsOkResponse`).
* **The model gap.** `bind_port_unmodeled`: LPS's `bind` of a fresh socket to this address
  (port 8080) has exactly one outcome, `unmodeled`. So under `Lps.ociRuntime` a run that reaches
  `bind` ends in `undefined unmodeled`, and `Task.servesImage` stays open until the runtime
  model's `bind` covers the declared port.

What `examples/containers/http-serve/docker-test.sh` tests (not proves): Docker loads the image
with the proved ID, the container listens on 8080 itself, `curl` receives exactly the 40-octet
response, and the container exits 0.
-/

public section

set_option maxRecDepth 100000

namespace Silmaril.Containers.HttpServe

open Silmaril.Containers Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Probes

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest :=
  Silmaril.Proofs.Containers.HttpServe.elf_digest

theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest :=
  Silmaril.Proofs.Containers.HttpServe.layer_digest

theorem config_digest : Silmaril.Crypto.sha256 config = configDigest :=
  Silmaril.Proofs.Containers.HttpServe.config_digest

theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest :=
  Silmaril.Proofs.Containers.HttpServe.manifest_digest

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer :=
  Silmaril.Proofs.Containers.HttpServe.layer_encode

theorem loadElf_elf : loadElf elf = some probe.snapshot :=
  Silmaril.Proofs.Containers.HttpServe.loadElf_elf

theorem runtime_load : ociRuntime.load image = .ok probe.snapshot :=
  Silmaril.Proofs.Containers.HttpServe.runtime_load

/-- The configuration the reader returns declares `8080/tcp`, the HTTP/1.1 interface's port. -/
theorem declared : ∃ f, Oci.load layout manifestDigest = .ok f ∧ f.config.exposed = [HttpOnce.port] ∧
    Http.Fixtures.httpIface.Declared f.config := by
  obtain ⟨f, hl, -, -, he⟩ := Silmaril.Proofs.Containers.HttpServe.oci_load
  exact ⟨f, hl, he, by rw [Http.Iface.Declared, he]; exact List.mem_singleton_self _⟩

theorem addr_in_image : (probe.bytes.drop 374).take 16 = addrBytes :=
  Silmaril.Proofs.Containers.HttpServe.addr_in_image

theorem response_in_image :
    ((probe.bytes.drop 390).take 40).map UInt8.ofBitVec = Fixtures.okResponse :=
  Silmaril.Proofs.Containers.HttpServe.response_in_image

/-- **The model gap**: LPS's `bind` to port 8080 is `unmodeled`. -/
theorem bind_port_unmodeled (fd addrp : Word) (i : SyscallInput) (m : Silmaril.Process.LPS.Model)
    (o : Silmaril.Process.LPS.Outcome SyscallEffect) (hfd : fdLookup m.fds fd = some (.socket .fresh))
    (hmem : readBytesMap i.mem addrp 16 = some addrBytes) :
    bindSpec fd addrp 16 i m o ↔ o = .unmodeled :=
  Silmaril.Proofs.Containers.HttpServe.bind_port_unmodeled fd addrp i m o hfd hmem

/-- **A successful session sends exactly the response** on its connection, as the server
platform reads it. -/
theorem sessionOk_sent {t : List Ev} {c : UInt8} (h : SessionOk t c) :
    ∃ ch : Word, Servers.Platform.sent ch.toNat (Http.sockTrace t) = Fixtures.okResponse :=
  Silmaril.Proofs.Containers.HttpServe.sessionOk_sent h

/-- **And that is one exact HTTP/1.1 response.** -/
theorem sessionOk_exact {t : List Ev} {c : UInt8} (h : SessionOk t c) :
    ∃ ch : Word, HttpOnce.IsOkResponse (Servers.Platform.sent ch.toNat (Http.sockTrace t)) := by
  obtain ⟨ch, hs⟩ := sessionOk_sent h
  exact ⟨ch, hs ▸ HttpOnce.okResponse_exact⟩

end Silmaril.Containers.HttpServe
