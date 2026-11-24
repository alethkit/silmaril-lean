module

import Silmaril.RiscV.OperationalInstitution.LPS.Thms
import Silmaril.Wasm.Institution.Operational.Thms
import Silmaril.X86.OperationalInstitution.Thms

open CategoryTheory Silmaril.Logic.Operational
open Silmaril.RiscV.LPS Silmaril.RiscV.OperationalInstitution.LPS

-- Four-byte little-endian loads into a0 from 0(a1); the second byte selects the width.
private def text (secondByte : Byte) : Segment :=
  ⟨0, 4, ⟨true, false, true⟩, #[some 0x03, some secondByte, some 0x05, some 0x00]⟩

private def dataSegment : Segment :=
  ⟨256, 8, ⟨true, true, false⟩, #[some 42, some 0, some 0, some 0, some 0, some 0, some 0, some 0]⟩

-- ld a0, 0(a1), in little-endian byte order.
private def loadedSegments : List Segment := [text 0xb5, dataSegment]

private def initial : MachineState where
  regs := BvMap.set (11 : Reg) (256 : Word) (BvMap.empty (n := 5))
  fregs := BvMap.empty (n := 5)
  pcVal := 0
  svcPending := none
  resv := none
  fcsr := 0
  mem address := if address = 256 then some 43 else none
  rom address := if address = 256 then some 42 else if address = 257 then some 0 else none

private def loadView : Label × Option MachineState :=
  resultView (stepAccesses loadedSegments initial)

example : initial.readByte 256 = some 43 := rfl
example : initial.readByte 257 = some 0 := rfl
example : loadView.1 = .advance [(256, 8)] := by decide
example : loadView.2.map (fun s => (s.reg 10, s.pc)) = some (43, 4) := by decide

private def highBitByte : MachineState :=
  { initial with mem := fun addr => if addr = 256 then some 0x80 else initial.mem addr }

-- lb and lbu a0, 0(a1) read the same overlay byte with different extension.
private def signedByteLoad :=
  resultView (stepAccesses [text 0x85, dataSegment] highBitByte)

private def unsignedByteLoad :=
  resultView (stepAccesses [text 0xc5, dataSegment] highBitByte)

example : signedByteLoad.1 = .advance [(256, 1)] := by decide
example : unsignedByteLoad.1 = .advance [(256, 1)] := by decide
example : signedByteLoad.2.map (fun s => s.reg 10) = some 0xffffffffffffff80 := by decide
example : unsignedByteLoad.2.map (fun s => s.reg 10) = some 0x80 := by decide

private theorem loadEdge :
    (system loadedSegments).model (encode (some initial), loadView.1, encode loadView.2) :=
  (step_iff loadedSegments initial loadView.1 loadView.2).2 rfl

private def missingImageBytes : Segment :=
  ⟨0, 4, ⟨true, false, true⟩, #[none, none, none, none]⟩

example : (system []).model (encode (some { initial with pcVal := 1 }), .fault, encode none) :=
  (step_iff [] _ .fault none).2 rfl

example : (system [missingImageBytes]).model (encode (some initial), .unmodeled, encode none) :=
  (step_iff [missingImageBytes] initial .unmodeled none).2 rfl

example : ¬ (system [missingImageBytes]).model (encode (some initial), .fault, encode none) := by
  intro h
  have tags := congrArg Prod.fst ((step_iff [missingImageBytes] initial .fault none).1 h)
  change Label.fault = Label.unmodeled at tags
  cases tags

-- A common observation keeps the origin, exposes one result register, and
-- presents each backend's byte view over word-sized addresses.
private abbrev observedShape (σ : Type) : RegisterShape :=
  ⟨Option σ ⊕ Option MachineState, Unit, Word, Word, Byte, Unit ⊕ Label⟩

private def x86View (σ : Type) : Silmaril.X86.OperationalInstitution.shape σ ⟶ observedShape σ :=
  ⟨Sum.inl, fun _ => Silmaril.X86.Reg.rax, id, BitVec.toNat, id, Sum.inl⟩

private def rv64View (σ : Type) : shape ⟶ observedShape σ :=
  ⟨Sum.inr, fun _ => (10 : Reg), id, id, id, Sum.inr⟩

private def image {A B : Signature} (f : A ⟶ B) (M : A.Model) : B.Model :=
  fun edge => ∃ source, M source ∧ Signature.mapEdge f source = edge

private def observed {σ : Type} (A : Silmaril.X86.RelIsa σ) (segs : List Segment) :
    RegisterSystem :=
  ⟨observedShape σ, fun e =>
    image (RegisterShape.signatures.map (x86View σ))
        (Silmaril.X86.OperationalInstitution.system A).model e ∨
      image (RegisterShape.signatures.map (rv64View σ)) (system segs).model e⟩

private def observeX86 {σ : Type} (A : Silmaril.X86.RelIsa σ) (segs : List Segment) :
    Silmaril.X86.OperationalInstitution.system A ⟶ observed A segs where
  shape := x86View σ
  preserves h := Or.inl ⟨_, h, rfl⟩

private def observeRV64 {σ : Type} (A : Silmaril.X86.RelIsa σ) (segs : List Segment) :
    system segs ⟶ observed A segs where
  shape := rv64View σ
  preserves h := Or.inr ⟨_, h, rfl⟩

example {σ : Type} (A : Silmaril.X86.RelIsa σ) :
    (observed A loadedSegments).model
      (RegisterShape.mapConfig (rv64View σ) (encode (some initial)),
        .inr loadView.1, RegisterShape.mapConfig (rv64View σ) (encode loadView.2)) :=
  (observeRV64 A loadedSegments).preserves loadEdge

example {σ : Type} :
    (RegisterShape.mapConfig (rv64View σ) (encode (some initial))).memory 256 = some 43 :=
  rfl

example {σ : Type} :
    (loadView.2.map fun s =>
      (RegisterShape.mapConfig (rv64View σ) (encode (some s))).registers ()) = some 43 := by
  change loadView.2.map (fun s => s.reg 10) = some 43
  decide

example {σ : Type} (A : Silmaril.X86.RelIsa σ) (s : σ) :
    (RegisterShape.mapConfig (x86View σ) (Silmaril.X86.OperationalInstitution.encode A.toViews (some s))).registers ()
      = (A.core s).read .rax :=
  rfl

example {σ : Type} (A : Silmaril.X86.RelIsa σ) (s : σ) (live : A.live s) (stop : A.step s .stop) :
    (observed A []).model
      (RegisterShape.mapConfig (x86View σ) (Silmaril.X86.OperationalInstitution.encode A.toViews (some s)),
        .inl (), RegisterShape.mapConfig (x86View σ) (Silmaril.X86.OperationalInstitution.encode A.toViews none)) :=
  (observeX86 A []).preserves ((Silmaril.X86.OperationalInstitution.stop_iff A s).2 ⟨live, stop⟩)

-- Aggregate x86 and Wasm observations with disjoint state and label tags.
-- This is a target for trace consumers with an origin field.
private abbrev taggedSig (A B : Signature) : Signature :=
  ⟨A.State ⊕ B.State, A.Label ⊕ B.Label⟩

private def taggedModel {A B : Signature} (M : A.Model) (N : B.Model) : (taggedSig A B).Model
  | (.inl s, .inl l, .inl t) => M (s, l, t)
  | (.inr s, .inr l, .inr t) => N (s, l, t)
  | _ => False

private def origin {α β : Type} : α ⊕ β → Bool
  | .inl _ => false
  | .inr _ => true

private theorem taggedEdgeOrigin {A B : Signature} {M : A.Model} {N : B.Model}
    {s t : (taggedSig A B).State} {l : (taggedSig A B).Label}
    (h : taggedModel M N (s, l, t)) : origin s = origin l ∧ origin s = origin t := by
  cases s <;> cases l <;> cases t <;> simp_all [taggedModel, origin]

-- Every state reached by a finite run and every label in the run keeps the source origin.
private theorem taggedRunOrigin {A B : Signature} {M : A.Model} {N : B.Model}
    {s t : (taggedSig A B).State} {ls : List (taggedSig A B).Label}
    (h : Runs (taggedModel M N) s ls t) : origin s = origin t ∧ ∀ l ∈ ls, origin s = origin l := by
  induction h with
  | refl => simp
  | stepL step _ ih =>
    obtain ⟨labelOrigin, nextOrigin⟩ := taggedEdgeOrigin step
    refine ⟨nextOrigin.trans ih.1, ?_⟩
    intro l mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact labelOrigin
    · exact nextOrigin.trans (ih.2 l mem)

private abbrev asTransition {C : Type 1} [Category.{0} C] {F : C ⥤ Signature}
    (S : System F) : TransitionSystem :=
  ⟨F.obj S.shape, S.model⟩

private abbrev tagged (A B : TransitionSystem) : TransitionSystem :=
  ⟨taggedSig A.shape B.shape, taggedModel A.model B.model⟩

private def tagLeft (A B : TransitionSystem) : A ⟶ tagged A B where
  shape := ⟨Sum.inl, Sum.inl⟩
  preserves := by rintro ⟨_, _, _⟩ h; exact h

private def tagRight (A B : TransitionSystem) : B ⟶ tagged A B where
  shape := ⟨Sum.inr, Sum.inr⟩
  preserves := by rintro ⟨_, _, _⟩ h; exact h

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics in
private theorem taggedWasmNop {H σ : Type} (P : Profile) (host : HostSemantics H)
    (X : Silmaril.X86.RelIsa σ) (s : Store H) (f : Frame) :
    let wasm := asTransition (Silmaril.Wasm.Institution.Operational.system P host)
    let x86 := asTransition (Silmaril.X86.OperationalInstitution.system X)
    let src := Silmaril.Wasm.Institution.Operational.encode ⟨s, f, [.plain .nop]⟩
    let dst := Silmaril.Wasm.Institution.Operational.encode ⟨s, f, []⟩
    Runs (tagged x86 wasm).model (.inr src) [.inr ()] (.inr dst) := by
  intro wasm x86 src dst
  have h : Runs wasm.model src [()] dst :=
    .stepL ((Silmaril.Wasm.Institution.Operational.step_iff P host _ _).2 (.parametric .nop)) .refl
  exact System.Hom.runs (tagRight x86 wasm) h

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics in
example {H σ : Type} (P : Profile) (host : HostSemantics H)
    (X : Silmaril.X86.RelIsa σ) (s : σ) (live : X.live s) (stop : X.step s .stop) :
    let x86 := asTransition (Silmaril.X86.OperationalInstitution.system X)
    let wasm := asTransition (Silmaril.Wasm.Institution.Operational.system P host)
    let src := Silmaril.X86.OperationalInstitution.encode X.toViews (some s)
    let dst := Silmaril.X86.OperationalInstitution.encode X.toViews none
    Runs (tagged x86 wasm).model (.inl src) [.inl ()] (.inl dst) := by
  intro x86 wasm src dst
  have h : Runs x86.model src [()] dst :=
    .stepL ((Silmaril.X86.OperationalInstitution.stop_iff X s).2 ⟨live, stop⟩) .refl
  exact System.Hom.runs (tagLeft x86 wasm) h

example {A B : Signature} (M : A.Model) (N : B.Model) (s : A.State) (l : A.Label) (t : B.State) :
    ¬ taggedModel M N (.inl s, .inl l, .inr t) :=
  id

example {A B : Signature} (M : A.Model) (N : B.Model) (s t : A.State) (l : B.Label) :
    ¬ taggedModel M N (.inl s, .inr l, .inl t) :=
  id
