module

public import Silmaril.Containers.HttpServe.Defs
public import Silmaril.Containers.Lps.Thms
public import Silmaril.Containers.Image.Thms
public import Silmaril.Containers.HttpOnce.Thms
public import Silmaril.Process.LPS.MonadIff

/-!
# Proofs: the self-contained HTTP server

Proofs for `Silmaril.Containers.HttpServe.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

set_option maxRecDepth 100000

namespace Silmaril.Proofs.Containers.HttpServe

open Silmaril.Containers Silmaril.Containers.HttpServe Silmaril.Containers.Lps
open Silmaril.Process.LPS Silmaril.Process.LPS.Machines Silmaril.Process.LPS.Probes

/-! ## Content digests (kernel-checked SHA-256) -/

theorem elf_digest : Silmaril.Crypto.sha256 elf = elfDigest := by decide +kernel
theorem layer_digest : Silmaril.Crypto.sha256 layer = layerDigest := by decide +kernel
theorem config_digest : Silmaril.Crypto.sha256 config = configDigest := by decide +kernel
theorem manifest_digest : Silmaril.Crypto.sha256 manifest = manifestDigest := by decide +kernel

theorem layer_encode : Silmaril.Formats.Tar.encode [entry] = some layer := by decide +kernel

/-! ## The ELF loads to the probe's snapshot -/

theorem probeLayout : probe.Layout := by probe_layout

theorem parse_map : (ELFImage.parse ELFImage.x86Policy (elfBytes elf)).map
    (·.x86Snapshot (elfBytes elf)) = some probe.snapshot := by rfl

theorem imageWf_native : ImageWf x86ExtNative probe.snapshot.image := by
  have v := probe.snapshot_valid probeLayout
  refine ⟨v.2.2.2.2.1, ?_, by decide +kernel⟩
  simp only [imagePhdrsReadable, v.2.2.2.2.2, Bool.and_true]
  decide +kernel

theorem loadElf_elf : loadElf elf = some probe.snapshot := by
  unfold loadElf ELFImage.loadX86
  have h := parse_map
  cases hp : ELFImage.parse ELFImage.x86Policy (elfBytes elf) with
  | none => rw [hp] at h; cases h
  | some r =>
    rw [hp] at h
    have hs : r.x86Snapshot (elfBytes elf) = probe.snapshot := Option.some.inj h
    have hi : r.image (elfBytes elf) = probe.snapshot.image := by rw [← hs]; rfl
    show (if ImageWf x86ExtNative (r.image (elfBytes elf)) then some (r.x86Snapshot (elfBytes elf))
      else none) = some probe.snapshot
    rw [hi]
    simp only [imageWf_native, ↓reduceIte, hs]

/-! ## The OCI image -/

theorem oci_entry : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.entryPath) =
    some (some ["http-serve"]) := by decide +kernel

theorem oci_root : ((Oci.load layout manifestDigest).toOption.map fun f => f.root ["http-serve"]) =
    some (some (.file elf true)) := by decide +kernel

theorem oci_exposed : ((Oci.load layout manifestDigest).toOption.map fun f => f.config.exposed) =
    some [HttpOnce.port] := by decide +kernel

theorem oci_load : ∃ f, Oci.load layout manifestDigest = .ok f ∧
    f.config.entryPath = some ["http-serve"] ∧ f.root ["http-serve"] = some (.file elf true) ∧
    f.config.exposed = [HttpOnce.port] := by
  have h₁ := oci_entry
  have h₂ := oci_root
  have h₃ := oci_exposed
  cases hl : Oci.load layout manifestDigest with
  | error r => rw [hl] at h₁; cases h₁
  | ok f =>
    rw [hl] at h₁ h₂ h₃
    exact ⟨f, rfl, Option.some.inj h₁, Option.some.inj h₂, Option.some.inj h₃⟩

theorem runtime_load : ociRuntime.load image = .ok probe.snapshot := by
  obtain ⟨f, hl, he, hr, -⟩ := oci_load
  show (Oci.load layout manifestDigest).bind runtime.load = _
  rw [hl]
  show runtime.load f = _
  have hp := Shape.entry_program (k := .static) (dec := loadElf) he hr
  simp only [runtime, hp, loadElf_elf]

/-- The response is in the loaded image, where the program points `sendto` at. -/
theorem response_in_image : ((probe.bytes.drop 390).take 40).map UInt8.ofBitVec = Fixtures.okResponse := by
  decide +kernel

/-- The address bytes are in the loaded image, where the program points `bind` at. -/
theorem addr_in_image : (probe.bytes.drop 374).take 16 = addrBytes := by decide +kernel

/-! ## LPS's `bind` to port 8080 -/

theorem bind_port_unmodeled (fd addrp : Word) (i : SyscallInput) (m : Model)
    (o : Outcome SyscallEffect) (hfd : fdLookup m.fds fd = some (.socket .fresh))
    (hmem : readBytesMap i.mem addrp 16 = some addrBytes) :
    bindSpec fd addrp 16 i m o ↔ o = .unmodeled := by
  unfold bindSpec
  rw [Sys.bind_input_iff, Sys.bind_getModel_iff]
  have hal : sint32 (16 : Word) = 16 := by decide
  have hz : zw (16 : Int) = 16 := by decide
  simp only [hfd, hal, hz, hmem]
  have h1 : ¬ ((16 : Int) < 0 ∨ SOCKADDR_STORAGE_SIZE < 16) := by decide
  have h2 : ¬ ((16 : Int) = 0) := by decide
  have h3 : ¬ ((16 : Int) < SOCKADDR_IN_SIZE) := by decide
  have h4 : ¬ ¬ (saFamilyOf addrBytes = AF_INET ∨
      (saFamilyOf addrBytes = AF_UNSPEC ∧ sinAddrOf addrBytes = INADDR_ANY)) := by decide
  have h5 : ¬ (sinAddrOf addrBytes ≠ INADDR_ANY) := by decide
  have h6 : sinPortOf addrBytes ≠ 0 := by decide
  simp only [h1, h2, h3, h4, h5, h6, ↓reduceIte, ne_eq, not_false_eq_true]
  unfold recordCopyins
  cases o with
  | ok y m₂ evs => simp only [Sys.bind, Sys.unmodeled, reduceCtorEq, false_and, exists_false]
  | unmodeled => simp [Sys.bind, Sys.unmodeled]

/-! ## A successful session, read by the server platform -/

theorem sockTrace_recv (ch : Word) (bs : List UInt8) :
    Http.sockTrace (recvEvs (connSock ch) bs) = bs.map fun b => .recv ch.toNat [b] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [recvEvs, List.map_cons, Http.sockTrace, List.filterMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem sockTrace_send (ch : Word) (bs : List UInt8) :
    Http.sockTrace (sendEvs (connSock ch) bs) = bs.map fun b => .send ch.toNat [b] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [sendEvs, List.map_cons, Http.sockTrace, List.filterMap_cons] at ih ⊢
    rw [ih]
    rfl

theorem sent_recvs (c : Nat) (bs : List UInt8) (t : List Servers.Platform.SockEv) :
    Servers.Platform.sent c ((bs.map fun b => .recv c [b]) ++ t) = Servers.Platform.sent c t := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [Servers.Platform.sent] using ih

theorem sent_sends (c : Nat) (bs : List UInt8) :
    Servers.Platform.sent c (bs.map fun b => .send c [b]) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [Servers.Platform.sent] using ih

theorem sessionOk_sent {t : List Ev} {c : UInt8} (h : SessionOk t c) :
    ∃ ch : Word, Servers.Platform.sent ch.toNat (Http.sockTrace t) = Fixtures.okResponse := by
  obtain ⟨-, ch, req, rfl⟩ := h
  refine ⟨ch, ?_⟩
  rw [Http.sockTrace, List.filterMap_append, ← Http.sockTrace, ← Http.sockTrace, sockTrace_recv,
    sockTrace_send, sent_recvs, sent_sends]

end Silmaril.Proofs.Containers.HttpServe
