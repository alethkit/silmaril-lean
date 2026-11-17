module

public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.Defs
public import Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

/-!
# A chunked parser with a ring buffer in linear memory: soundness

* `chunkRing_instance`, `ringInv_init`: the example validates, instantiates, and its
  instantiated store represents the empty buffer.
* **Stateful Hoare-logic specification** (`chunkRing_sat`): in every environment `ρ` and every
  profile, for every parsing policy, assuming writer answers agree with `ρ` (no writer sentinel),
  `chunkRing` meets `chunkSSpec ringPix ppol ρ takeR ringInv`: the store invariant `ringInv`
  reads the chunk buffer (up to eight values) off the two globals and the `i64` slots of linear
  memory; `finish(n)` with `0 < n ≤` the buffered count returns `(n, h)` with `h` denoting the
  list of the oldest `n` buffered values and leaves the rest buffered; otherwise it returns
  `(0, h)`, `h` denoting `()`.
* **Soundness** (`chunkRing_sound`, store semantics, writer policies without a sentinel or UB;
  `chunkRing_fixed_sound`, fixed environments, writer policies without a sentinel): every pair is
  `(vs, SExp2.ofAtoms vs)`, the values consumed by one `finish`, in order (`chunkRing_rel`).

Non-vacuity is not proved here: the replay used for `chunkTake`
(`Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.mem_moduleMixedRel_of_replaySeqC`, by kernel
evaluation of the interpreter) does not scale to a module with a memory page: a single
`i64.store` followed by a load on a 65536-byte `ByteArray` does not finish in kernel evaluation
within ten minutes (the byte array is a list in the kernel, and `ByteArray.copySlice` rebuilds
it element by element).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Accept.Parse
  Silmaril.Wasm.Game.HandleAccept.Mixed Silmaril.Wasm.Game.HandleAccept.Mixed.Stream
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Parsing Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk
  Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Take

theorem chunkRing_instance : (Verify.instance? chunkRing).isSome = true := by decide +kernel

theorem ringInv_init : ringInv [] (Verify.instOf chunkRing).store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.ringInv_init

/-- **`chunkRing` meets its chunk specification.** -/
theorem chunkRing_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (ppol : PPolicy (BitVec 32)) :
    SGameSat P (Verify.instOf chunkRing) (mixedISpec twoIx none ρ)
      (chunkSSpec ringPix ppol ρ takeR ringInv) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring.chunkRing_sat P ρ ppol

/-- **`chunkRing` relates only `(vs, (vs))`** (store semantics). -/
theorem chunkRing_sound (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) :
    moduleMixedRel P chunkRing twoIx ringPix pol ppol ⊆ takeR :=
  moduleMixedRel_sound_of_chunkSat (Inv := fun _ => ringInv)
    (fun ρ => hsen ▸ chunkRing_sat P ρ ppol) (fun _ => ringInv_init) hw ha hb ho

/-- **`chunkRing` relates only `(vs, (vs))` over fixed environments**, for every writer policy
without a sentinel. -/
theorem chunkRing_fixed_sound (P : Profile) {pol : Policy (BitVec 32)}
    (hsen : pol.sentinel = none) {ppol : PPolicy (BitVec 32)} (hb : ppol.onBadHandle ≠ .ub)
    (ho : ppol.onOverrun ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    moduleMixedFixedRel P chunkRing twoIx ringPix pol ppol Envs ⊆ takeR :=
  moduleMixedFixedRel_sound_of_chunkSat (Inv := fun _ => ringInv)
    (fun ρ _ => hsen ▸ chunkRing_sat P ρ ppol) (fun _ _ => ringInv_init) hb ho

/-- Every related pair, read off. -/
theorem chunkRing_rel (P : Profile) {pol : Policy (BitVec 32)} (hsen : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) {ppol : PPolicy (BitVec 32)}
    (hb : ppol.onBadHandle ≠ .ub) (ho : ppol.onOverrun ≠ .ub) {w : List (BitVec 64)}
    {t : SExp2 (BitVec 64)} (h : (w, t) ∈ moduleMixedRel P chunkRing twoIx ringPix pol ppol) :
    t = SExp2.ofAtoms w :=
  chunkRing_sound P hsen hw ha hb ho h

end Silmaril.Wasm.Game.HandleAccept.Mixed.Chunk.Ring
