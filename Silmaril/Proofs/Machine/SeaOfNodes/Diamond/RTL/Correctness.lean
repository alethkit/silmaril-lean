module

public import Silmaril.Machine.SeaOfNodes.Diamond.RTL.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.Thms

public section

namespace Silmaril.Machine.SeaOfNodes.Diamond.RTL.Proofs

open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow Graph Projection Val ValueSort dataPorts read sortValue)
open Silmaril.SSA.RVSDG (Locals Origin Port PortType Tuple Wires extend)
open Silmaril.Machine.Lir (Memory Word ofBool)
open Silmaril.Machine.RTL (CallOracle Frame)
open Silmaril.Machine.RTL.SSA (Func Op Prog)

variable {sigs past : List (List PortTy)}

/-- The frame stores numeric predicates as the existing RTL comparison does.
Control ports are absent from the admitted source, but the invariant works on
an open prefix of the source's generic typed store. -/
private def encode : (t : PortTy) → Val model.value t → Word
  | .value .predicate, b => ofBool b.down
  | .value (.data _), w => w
  | .control _, n => BitVec.ofNat 64 n.down.val
  | .state e, _ => nomatch e

private def ArgsMatch (fr : Frame Reg) (x y : Word) : Prop :=
  ∀ {t : PortTy} (p : Port args t),
    fr.get (.arg (portIndex p)) = some (encode t ((entry x y).get p))

private def LocalsMatch (fr : Frame Reg) (base : Nat) :
    {past : List (List PortTy)} → Locals (Val model.value) past → Prop
  | [], _ => True
  | _ :: _, xs =>
    (∀ {t : PortTy} (p : Port _ t), fr.get (.node base) = some (encode t (xs.1.get p))) ∧
      LocalsMatch fr (base + 1) xs.2

private def initialFrame (x y : Word) : Frame Reg :=
  (Frame.empty.set (.arg 0) x).set (.arg 1) y

private theorem initial_args (x y : Word) : ArgsMatch (initialFrame x y) x y := by
  intro t p
  cases p with
  | head => rfl
  | tail p =>
    cases p with
    | head => rfl
    | tail p => nomatch p

private theorem locals_read {fr : Frame Reg} {base : Nat} {t : PortTy}
    (xs : Locals (Val model.value) past) (matched : LocalsMatch fr base xs)
    (i : Fin past.length) (p : Port past[i] t) :
    fr.get (.node (base + i.val)) = some (encode t ((xs.get i).get p)) := by
  induction past generalizing base with
  | nil => exact i.elim0
  | cons head tail ih =>
    cases i using Fin.cases with
    | zero => exact matched.1 p
    | succ i =>
      change fr.get (.node (base + i.succ.val)) = some (encode t ((xs.2.get i).get p))
      simpa only [Fin.val_succ, Nat.add_succ, Nat.succ_add] using
        ih xs.2 matched.2 i p

private theorem read_origin {x y : Word} {fr : Frame Reg} {t : PortTy}
    {xs : Locals (Val model.value) past} (ha : ArgsMatch fr x y) (hl : LocalsMatch fr 0 xs)
    (w : Origin args past t) :
    fr.get (register w) = some (encode t (read model w (entry x y) xs)) := by
  cases w with
  | arg p => exact ha p
  | output i p =>
    change fr.get (.node i.val) = some (encode t ((xs.get i).get p))
    simpa only [Nat.zero_add] using locals_read xs hl i p

private theorem append_local {fr : Frame Reg} {base : Nat} {out : ValueSort Unit}
    (xs : Locals (Val model.value) past) (v : sortValue model.value out)
    (matched : LocalsMatch fr base xs) :
    LocalsMatch (fr.set (.node (base + past.length)) (encode (.value out) v)) base
      (xs.snoc (Tuple.cons (F := Val model.value) (t := PortType.value out) v .nil)) := by
  induction past generalizing base with
  | nil =>
    constructor
    · intro t p
      cases p with
      | head =>
        simp
        rfl
      | tail p => nomatch p
    · exact trivial
  | cons head tail ih =>
    constructor
    · intro t p
      have fresh : base ≠ base + (head :: tail).length := by simp
      change (fr.set (.node (base + (head :: tail).length)) _).get (.node base) =
        some (encode t (xs.1.get p))
      simpa [Frame.get_set, fresh] using matched.1 p
    · have index : base + (head :: tail).length = base + 1 + tail.length := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact ih xs.2 matched.2

private theorem emit_exec {sorts : List (ValueSort Unit)} {out : ValueSort Unit} {x y : Word}
    (op : WordOp sorts out) (wires : Wires args past (dataPorts sorts))
    (fr : Frame Reg) (mem : Memory) (xs : Locals (Val model.value) past)
    (readWire : ∀ {t : PortTy} (wire : Origin args past t),
      fr.get (register wire) = some (encode t (read model wire (entry x y) xs))) :
    (emitOp (.node past.length) op wires).exec fr mem =
      some (fr.set (.node past.length) (encode (.value out) (model.run op (wires.read (entry x y) xs))), mem) := by
  cases op with
  | const v => cases wires; rfl
  | add | sub | eq =>
    cases wires with
    | cons left rest =>
      cases rest with
      | cons right tail =>
        cases tail
        simp only [emitOp, Op.exec, Tuple.get, readWire, Option.bind_some]
        rfl

private theorem simulate_ops (oracle : CallOracle) (x y : Word) (mem : Memory)
    (flow : Dataflow WordOp args past sigs) (fr : Frame Reg) (xs : Locals (Val model.value) past)
    (ha : ArgsMatch fr x y) (hl : LocalsMatch fr 0 xs) :
    ∃ final, Silmaril.Machine.RTL.SSA.Ops.Exec oracle (emitOps flow) fr mem final mem ∧ ArgsMatch final x y ∧
      LocalsMatch final 0 (flow.eval model (entry x y) xs) := by
  induction flow generalizing fr with
  | nil => exact ⟨fr, .nil, ha, hl⟩
  | @cons past sigs sorts out op wires rest ih =>
    let v := model.run op (wires.read (entry x y) xs)
    let next := fr.set (.node past.length) (encode (.value out) v)
    have next_args : ArgsMatch next x y := by
      intro t p
      simpa [next, Frame.get_set] using ha p
    have next_locals : LocalsMatch next 0
        (xs.snoc (Tuple.cons (F := Val model.value) (t := PortType.value out) v .nil)) := by
      simpa only [Nat.zero_add] using append_local (base := 0) xs v hl
    obtain ⟨final, steps, argsAgree, localsAgree⟩ := ih next _ next_args next_locals
    exact ⟨final, .op (emit_exec op wires fr mem xs (read_origin ha hl)) steps, argsAgree, localsAgree⟩

private theorem arm_block (g : WordDiamond sigs) (p : Projection) :
    (lowerFunc g).block? (armLabel p) = some (armBlock g p) := by
  cases p <;> rfl

private theorem exec_arm (g : WordDiamond sigs) (p : Projection) (fr : Frame Reg)
    (mem : Memory) (value : Word) (h : fr.get (incoming g p) = some value) :
    Func.Exec (lower g).oracle (lowerFunc g) (armLabel p) fr mem (.returned [value] mem) := by
  refine .jump (vals := [value]) (fr₂ := fr.set .phi value)
    (arm_block g p) .nil rfl ?_ rfl rfl ?_
  · simp [Frame.readAll, h]
  · refine .ret rfl .nil rfl ?_
    simp [Frame.readAll]

private theorem branch_label (b : Bool) :
    (if ofBool b = 0 then armLabel .onFalse else armLabel .onTrue) =
      armLabel (Projection.ofBool b) := by
  cases b <;> decide

private theorem exec_entry (g : WordDiamond sigs) (x y : Word) (mem : Memory) :
    Func.Exec (lower g).oracle (lowerFunc g) 0 (initialFrame x y) mem
      (.returned [g.denote model (entry x y)] mem) := by
  obtain ⟨fr, steps, ha, hl⟩ :=
    simulate_ops (lower g).oracle x y mem g.dataflow (initialFrame x y) PUnit.unit
      (initial_args x y) trivial
  let xs := g.dataflow.eval model (entry x y) PUnit.unit
  let b := (read model g.predicate (entry x y) xs).down
  let p := Projection.ofBool b
  have cond := read_origin ha hl g.predicate
  have arm := exec_arm g p fr mem _
    (read_origin ha hl (g.phi.operand (g.phi.merge.slot p)))
  refine .cond (b := entryBlock g) (bt := armBlock g p) (x := ofBool b) (vals := []) (fr₂ := fr)
    rfl steps rfl cond ?_ ?_ rfl ?_
  · simp [Frame.readAll]
  · rw [branch_label]
    exact arm_block g p
  · rw [branch_label]
    exact arm

private theorem emitted_returns (g : WordDiamond sigs) (x y : Word) (mem : Memory) :
    (lower g).oracle 0 [x, y] mem [g.denote model (entry x y)] mem :=
  (Func.exec_returned_iff_oracle (p := lower g) (f := 0) (fn := lowerFunc g)
    (b := entryBlock g) (args := [x, y]) (fr := initialFrame x y) rfl rfl rfl).mp (exec_entry g x y mem)

theorem lower_returns_iff (g : WordDiamond sigs) (x y : Word) (initial final : Memory)
    (returned : List Word) :
    (lower g).oracle 0 [x, y] initial returned final ↔
      ∃ value : Word, g.Returns model (entry x y) value ∧ returned = [value] ∧ final = initial := by
  have expected := emitted_returns g x y initial
  constructor
  · intro actual
    obtain ⟨valuesEq, memEq⟩ :=
      Prog.oracle_deterministic (lower g) 0 [x, y] initial _ _ _ _ actual expected
    exact ⟨g.denote model (entry x y), (g.returns_iff_denote model _ _).mpr rfl, valuesEq, memEq⟩
  · rintro ⟨value, h, rfl, rfl⟩
    rw [← (g.returns_iff_denote model _ _).mp h]
    exact expected

theorem lower_forward (g : WordDiamond sigs) {source target : Nat}
    (h : target ∈ (lowerFunc g).succ source) : source < target := by
  rcases source with _ | _ | _ | _ | source
  all_goals simp [Func.succ, Func.block?, lowerFunc, entryBlock, armBlock, joinBlock, armLabel,
    Silmaril.Machine.RTL.SSA.Term.successors] at h
  all_goals omega

end Silmaril.Machine.SeaOfNodes.Diamond.RTL.Proofs
