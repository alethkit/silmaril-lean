module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Capture.Refinement.Trace.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.PackedTrace.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.InstructionMap.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Ordered.Packed.Institution.Thms

/-! # Typed requests at the captured entry and the back edge -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Interaction.Examples

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG (Body Block Term)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Primitive Transfer BlockInput splitTransfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues ModelTree Compatible)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree Trace TraceLE HasTrace vis vis_bind diverge diverge_bind iterate_fixpoint
    traceLE_diverge hasTrace_diverge_iff hasTrace_vis_exchange_iff hasTrace_vis_request
    iterate_pure_loop out_ret)
open LambdaSSA.FiniteCFG (packedExecutionRegion packedExecution_tree packedTreeOutput)

private abbrev SortName := ULift.{1} Unit
private abbrev Atom := ULift.{1} Nat
private abbrev Reg := ULift.{1} Unit
private abbrev Label := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))
private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩

private inductive Opcode
  | seed
  | tick
  | capture

private inductive Event : Type → Type
  | call (op : Opcode) (arg : Nat) : Event Nat
  | capture : Event Nat
  | malformed (op : Opcode) : Event Empty

private def num : Ty SortName := .base ⟨()⟩
private def captures : BoundCtx (Ty SortName) 1 := .snoc .nil num
private def edgeType : Ty SortName := .product num .unit
private def inputType : Ty SortName := LambdaSSA.Region.packedInputType captures.toList

private instance : HasTy Opcode (Ty SortName) where
  src
    | .capture => .unit
    | .seed | .tick => num
  trg
    | .capture => inputType
    | .seed | .tick => num

private def typed : Silmaril.Isotope.Semantics.InstructionModel
    (Ty.denote (AtomValues.carrier (κ := SortName))) Opcode (ModelTree Event) where
  eval
    | .seed, arg => vis (.call .seed arg.down) fun reply => pure (ULift.up reply)
    | .tick, arg => vis (.call .tick arg.down) fun reply => pure (ULift.up reply)
    | .capture, _ => vis .capture fun reply => pure (PUnit.unit, ULift.up reply)

private def instr : Primitive Event Opcode Runtime
  | .seed, .atom arg => vis (.call .seed arg.2.down) fun reply => pure (atom reply)
  | .tick, .atom arg => vis (.call .tick arg.2.down) fun reply => pure (atom reply)
  | .capture, .unit => vis .capture fun reply => pure (.pair .unit (atom reply))
  | op, _ => vis (.malformed op) Empty.elim

private theorem compatible : Compatible (κ' := SortName) typed instr := by
  intro op arg
  cases op with
  | seed =>
    change (vis (.call .seed arg.down) fun reply => pure (atom reply)) =
      ((vis (.call .seed arg.down) (fun reply => pure (ULift.up reply)) : Tree Event Atom) >>=
        fun v => pure (atom v.down))
    simp only [vis_bind, pure_bind]
  | tick =>
    change (vis (.call .tick arg.down) fun reply => pure (atom reply)) =
      ((vis (.call .tick arg.down) (fun reply => pure (ULift.up reply)) : Tree Event Atom) >>=
        fun v => pure (atom v.down))
    simp only [vis_bind, pure_bind]
  | capture =>
    change (vis .capture fun reply => pure (Value.pair .unit (atom reply))) =
      ((vis .capture (fun reply => pure (PUnit.unit, ULift.up reply)) : Tree Event (PUnit × Atom)) >>=
        fun v => pure (Value.pair .unit (atom v.2.down)))
    simp only [vis_bind, pure_bind]

private def reg : Reg := ⟨()⟩
private def header : Label := ⟨10⟩
private def back : Label := ⟨20⟩
private def exitLabel : Label := ⟨99⟩

private def source : CFG Reg Label Opcode :=
  ⟨.let1 reg (.app .seed (.var reg)) (.term (.br header (.var reg))),
    [(header, ⟨reg, .term (.br back (.var reg))⟩),
     (back, ⟨reg, .let1 reg (.app .tick (.var reg)) (.term (.br header (.var reg)))⟩)]⟩

private def names : Fin 1 → Reg := fun _ => reg
private abbrev generated := CFG.Cyclic.Versioning.compile source

private def admitted := (compileTyped source [exitLabel] names captures
  (fun _ => edgeType) (fun _ => num)).get (by decide)

private def store (capture : Nat) : Reg × Nat → Value Runtime := fun _ => atom capture
private def env (capture : Nat) : Env Runtime := fun _ => atom capture
private def ambient : Env Runtime := fun _ => .unit
private def packet (n : Nat) : Value Runtime := .pair (atom n) .unit

private def packetRead : LetCase.LocallyNameless.Tm Empty Opcode 0 := .op .capture .unit

private def closed := (Capture.close captures (fun _ => edgeType) (fun _ => num)
  admitted.val admitted.property.2 packetRead
  (show LetCase.LocallyNameless.HasType Opcode .nil .nil packetRead inputType from .op .unit)).get (by decide)

private theorem entry_requests (capture : Nat) :
    region instr (env capture) admitted.val.entry.erase =
      vis (.call .seed capture) (fun reply => pure (0, packet reply)) := by
  change region instr (env capture)
    (.let₁ (.op .seed (.var 0)) (.br 0 (.pair (.var 0) .unit))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, env, instr,
    LambdaSSA.Semantics.extend_zero, packet, atom]

example (capture : Nat) :
    (generated.entry.evalJump (treeModel instr) (store capture) >>=
      fun p => pure (treeNumber (labelIndex generated.blocks [exitLabel]) p)) =
      vis (.call .seed capture) (fun reply => pure (0, packet reply)) :=
  (entry_tree instr generated [exitLabel] (fun i => (names i, 0)) admitted.property.1
    (store capture) (env capture) (fun _ => rfl)).trans (entry_requests capture)

private def backIndex : Fin generated.blocks.length := ⟨1, by decide⟩

private theorem back_requests (capture argument : Nat) :
    region instr (extend (env capture) (packet argument)) (admitted.val.block backIndex).erase =
      vis (.call .tick argument) (fun reply => pure (0, packet reply)) := by
  change region instr (extend (env capture) (packet argument))
    (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit)))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, packet, instr, atom,
    LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ]

example (capture argument : Nat) :
    (CFG.Cyclic.stepSSA (treeModel instr) generated.blocks (store capture) (back, packet argument) >>=
      fun s => pure (s.map id (treeNumber (labelIndex generated.blocks [exitLabel])))) =
      vis (.call .tick argument) (fun reply => pure (.inr (0, packet reply))) := by
  rw [step_tree instr generated [exitLabel] (fun i => (names i, 0)) admitted.property.1
    back backIndex rfl (store capture) (env capture) (packet argument), back_requests, vis_bind]
  simp only [pure_bind]

private def captureProducer : Tree Event Atom :=
  vis .capture (fun reply => pure (ULift.up reply))

private theorem capture_packet :
    LambdaSSA.Semantics.Interaction.term instr ambient (Morphism.CaseSSA.erase packetRead) =
      (captureProducer >>= fun reply => pure (Capture.packEnv 1 (env reply.down))) := by
  change (LambdaSSA.Semantics.Interaction.term instr ambient (.op .capture .unit)) = _
  simp only [LambdaSSA.Semantics.Interaction.term, instr, pure_bind, captureProducer, vis_bind,
    Capture.packEnv, env]

-- The producer's reply becomes the seed operand and the seed reply becomes
-- the first edge packet.
example : region instr ambient closed.val.entry.erase =
    vis .capture (fun captured =>
      vis (.call .seed captured) (fun reply => pure (0, packet reply))) := by
  rw [Capture.entry_tree instr closed.property.2 capture_packet]
  simp only [captureProducer, vis_bind, pure_bind, entry_requests]

example (capture : Nat) :
    (CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel instr) generated (store capture) >>=
      fun p => pure (treeExitNumber [exitLabel] p)) = region instr (env capture) admitted.val.erase :=
  compile_run_tree instr source [exitLabel] names admitted.property.1
    (store capture) (env capture) (fun _ => rfl)

private noncomputable def openStep (capture : Nat) (p : BlockInput Runtime 2) :
    Tree Event (Transfer Runtime ⊕ BlockInput Runtime 2) :=
  region instr (extend (env capture) p.2) (admitted.val.block p.1).erase >>=
    fun out => pure (splitTransfer 2 out)

private theorem closed_tree :
    region instr ambient closed.val.erase =
      vis .capture (fun capture => region instr (env capture) admitted.val.erase) := by
  rw [Capture.graph_tree instr closed.property.2 capture_packet]
  simp only [captureProducer, vis_bind, pure_bind]

-- The general theorem preserves the named runner after each capture reply
-- and applies the dispatcher's encoding only to the eventual return.
example : region instr ambient (packedExecutionRegion closed.property.1) =
    vis .capture (fun capture => CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel instr) generated (store capture) >>=
      fun p => pure (packedTreeOutput (treeExitNumber [exitLabel] p))) := by
  let named : Tree Event (Transfer Runtime) := captureProducer >>= fun reply =>
    CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel instr) generated (store reply.down) >>=
      fun p => pure (packedTreeOutput (treeExitNumber [exitLabel] p))
  have h := (packed_run_tree_eq_iff_traceLE instr source [exitLabel] names
    (fun reply : Atom => store reply.down) admitted.property.1 (fun _ _ => rfl)
    closed.property.1 closed.property.2 capture_packet named).mpr
      ⟨TraceLE.refl named, TraceLE.refl named⟩
  simpa only [named, captureProducer, vis_bind, pure_bind] using h

private theorem tick_loop (capture argument : Nat) :
    iter (openStep capture) (0, packet argument) =
      vis (.call .tick argument) (fun reply => iter (openStep capture) (0, packet reply)) := by
  have headerStep : openStep capture (0, packet argument) = pure (.inr (1, packet argument)) := by
    change (region instr (extend (env capture) (packet argument))
      (.let₂ (.var 0) (.br 1 (.pair (.var 1) .unit))) >>= _) = _
    simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, packet,
      LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ]
    rfl
  have backStep : openStep capture (1, packet argument) =
      vis (.call .tick argument) (fun reply => pure (.inr (0, packet reply))) := by
    change (region instr (extend (env capture) (packet argument)) (admitted.val.block backIndex).erase >>= _) = _
    rw [back_requests, vis_bind]
    simp only [pure_bind]
    rfl
  calc
    _ = iter (openStep capture) (1, packet argument) := by
      rw [congrFun (iterate_fixpoint (openStep capture)) (0, packet argument)]
      rw [headerStep, pure_bind, Sum.elim_inr]
    _ = _ := by
      rw [congrFun (iterate_fixpoint (openStep capture)) (1, packet argument)]
      rw [backStep]
      simp only [vis_bind, pure_bind, Sum.elim_inr]

-- Two successive tick requests use the seed reply and then the first tick
-- reply as operands. The equality quantifies over all replies at each node.
example : region instr ambient (packedExecutionRegion closed.property.1) =
    vis .capture (fun capture => vis (.call .seed capture) (fun seed =>
      vis (.call .tick seed) (fun first =>
        vis (.call .tick first) (fun second => iter (openStep capture) (0, packet second) >>=
          fun p => pure (packedTreeOutput p))))) := by
  rw [packedExecution_tree, closed_tree, vis_bind]
  congr 1
  funext capture
  change ((region instr (env capture) admitted.val.entry.erase >>= fun out =>
      Sum.elim pure (iter (openStep capture)) (splitTransfer 2 out)) >>= _) = _
  rw [entry_requests]
  simp only [vis_bind, pure_bind]
  congr 1
  funext seed
  change (iter (openStep capture) (0, packet seed) >>= _) = _
  rw [tick_loop, vis_bind]
  congr 1
  funext first
  rw [tick_loop, vis_bind]

/-! ## Directed refinement at a seed reply -/

private def partialInstr : Primitive Event Opcode Runtime
  | .seed, .atom arg => vis (.call .seed arg.2.down) fun reply =>
      if reply = 0 then diverge else pure (atom reply)
  | op, value => instr op value

private theorem partial_capture_packet :
    LambdaSSA.Semantics.Interaction.term partialInstr ambient (Morphism.CaseSSA.erase packetRead) =
      (captureProducer >>= fun reply => pure (Capture.packEnv 1 (env reply.down))) :=
  capture_packet

private noncomputable def resume (capture seed : Nat) : Tree Event (Label × Value Runtime) :=
  iter (CFG.Cyclic.stepSSA (treeModel partialInstr) generated.blocks (store capture))
    (header, packet seed)

private theorem partial_named (capture : Nat) :
    CFG.Cyclic.runSSA (treeModel partialInstr) generated (store capture) =
      vis (.call .seed capture) (fun seed => if seed = 0 then diverge else resume capture seed) := by
  unfold CFG.Cyclic.runSSA
  have entry : generated.entry.evalJump (treeModel partialInstr) (store capture) =
      (partialInstr .seed (atom capture) >>= fun result => pure (header, .pair result .unit)) := by
    rfl
  rw [entry]
  simp only [partialInstr, atom, vis_bind, bind_assoc]
  congr 1
  funext seed
  by_cases h : seed = 0 <;> simp only [h, ite_true, ite_false, diverge_bind, pure_bind, resume, packet, atom]

private noncomputable def spec (capture : Atom) : Tree Event (Label × Value Runtime) :=
  vis (.call .seed capture.down) (fun seed =>
    if seed = 0 then pure (exitLabel, atom 0) else resume capture.down seed)

private theorem named_refines_spec (capture : Atom) :
    TraceLE (CFG.Cyclic.runSSA (M := ModelTree Event) (treeModel partialInstr) generated (store capture.down)) (spec capture) := by
  rw [partial_named]
  apply TraceLE.vis
  intro seed
  by_cases h : seed = 0
  · simpa only [spec, h, ite_true] using traceLE_diverge (pure (exitLabel, atom 0) : Tree Event (Label × Value Runtime))
  · simpa only [spec, h, ite_false] using TraceLE.refl (resume capture.down seed)

private def tag (p : Label × Value Runtime) : Transfer Runtime :=
  packedTreeOutput (treeExitNumber [exitLabel] p)

private noncomputable def packed : Tree Event (Transfer Runtime) :=
  region partialInstr ambient (packedExecutionRegion closed.property.1)

private noncomputable def packedSpec : Tree Event (Transfer Runtime) :=
  captureProducer >>= fun reply => spec reply >>= fun p => pure (tag p)

private def zeroSeedExit : Trace Event (Transfer Runtime) :=
  .exchange .capture 7 (.exchange (.call .seed 7) 0 (.result (0, .inl (atom 0))))

-- Both trees issue capture and seed. The specification returns the encoded
-- exit after capture reply 7 and seed reply 0, where the dispatcher goes silent.
example :
    letI := Tree.tracePartialOrder (E := Event) (A := Transfer Runtime)
    packed < packedSpec := by
  let _ : PartialOrder (Tree Event (Transfer Runtime)) := Tree.tracePartialOrder
  refine lt_of_le_not_ge (packed_run_tree_traceLE partialInstr source [exitLabel] names
    (fun reply : Atom => store reply.down) admitted.property.1 (fun _ _ => rfl)
    closed.property.1 closed.property.2 partial_capture_packet named_refines_spec) ?_
  have hspec : HasTrace packedSpec zeroSeedExit := by
    simp only [packedSpec, captureProducer, spec, zeroSeedExit, vis_bind, pure_bind,
      hasTrace_vis_exchange_iff, ite_true]
    exact out_ret ((0, .inl (atom 0)) : Transfer Runtime)
  have hpacked : ¬ HasTrace packed zeroSeedExit := by
    unfold packed
    rw [packed_run_tree partialInstr source [exitLabel] names (fun reply : Atom => store reply.down)
      admitted.property.1 (fun _ _ => rfl) closed.property.1 closed.property.2 partial_capture_packet]
    simp only [captureProducer, partial_named, zeroSeedExit, vis_bind, pure_bind,
      hasTrace_vis_exchange_iff, ite_true, diverge_bind, hasTrace_diverge_iff, reduceCtorEq, not_false_eq_true]
  exact fun h => hpacked (h zeroSeedExit hspec)

/-! ## Refinement of the actual packed feedback block -/

private def partialTick : Primitive Event Opcode Runtime
  | .tick, .atom arg => vis (.call .tick arg.2.down) fun reply =>
      if reply = 0 then diverge else pure (atom reply)
  | op, value => instr op value

private theorem tick_refines (value : Value Runtime) :
    TraceLE (partialTick .tick value) (instr .tick value) := by
  cases value with
  | atom arg =>
    apply TraceLE.vis
    intro reply
    by_cases h : reply = 0
    · simpa only [h, ite_true] using traceLE_diverge (pure (atom reply) : Tree Event (Value Runtime))
    · simpa only [h, ite_false] using TraceLE.refl (pure (atom reply) : Tree Event (Value Runtime))
  | _ => exact TraceLE.refl _

-- The capture and seed entry are common. Only the back-edge block can
-- acquire additional behavior after a tick reply.
example : TraceLE (region partialTick ambient (packedExecutionRegion closed.property.1))
    (region instr ambient (packedExecutionRegion closed.property.1)) := by
  apply LambdaSSA.FiniteCFG.packedExecution_traceLE _ _ _ _ closed.property.1 closed.property.1
  · exact TraceLE.refl _
  · intro i input
    have block : ∀ j : Fin 2, TraceLE
        (region partialTick (extend ambient input) (closed.val.block j).erase)
        (region instr (extend ambient input) (closed.val.block j).erase) := by
      intro j
      refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) j
      · exact TraceLE.refl _
      · change TraceLE (region partialTick (extend ambient input) (closed.val.block backIndex).erase)
          (region instr (extend ambient input) (closed.val.block backIndex).erase)
        rw [closed.property.2.block backIndex]
        change TraceLE
          (region partialTick (extend ambient input)
            (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit)))))
          (region instr (extend ambient input)
            (.let₂ (.var 0) (.let₁ (.op .tick (.var 1)) (.br 0 (.pair (.var 0) .unit)))))
        simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind,
          LambdaSSA.Semantics.extend_zero, LambdaSSA.Semantics.extend_succ]
        cases input with
        | pair arg _ => exact (tick_refines arg).bind_left _
        | _ => exact TraceLE.refl _
    exact block i

/-! ## Relabelling before executable closure and packing -/

open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Morphism (SignatureMap)

private instance : HasEff Opcode Bool := ⟨fun _ => true⟩

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event Opcode where
  instructions :=
    { denote := typed.eval
      denotePure := fun _ hf => Bool.noConfusion hf
      denote_pure := fun _ hf => Bool.noConfusion hf }
  raw := instr
  compatible := compatible

-- Both seed and tick now request tick. The capture operation keeps its profile.
private def rename : SignatureMap Opcode Opcode (Ty SortName) (Ty SortName) Bool Bool where
  instr
    | .seed | .tick => .tick
    | .capture => .capture
  ty := id
  eff := id
  source op := by cases op <;> rfl
  target op := by cases op <;> rfl
  effect _ := rfl

private theorem rename_types : rename.ty = id := rfl
private theorem rename_bottom : rename.eff ⊥ = ⊥ := rfl

private theorem captureInput : LetCase.LocallyNameless.HasType Opcode .nil .nil packetRead inputType :=
  .op .unit

private abbrev mappedInput := Capture.mapInput_hasType rename.instr
    (flatProfiles rename rename_types) captureInput

private def closedMapped := (Capture.close captures (fun _ => edgeType) (fun _ => num)
  (admitted.val.mapInstr rename.instr) (admitted.property.2.mapInstr (flatProfiles rename rename_types))
  (packetRead.mapInstr rename.instr) mappedInput).get (by decide)

private theorem closedMapped_eq : closedMapped.val = closed.val.mapInstr rename.instr := by
  have h := Capture.close_mapInstr rename.instr (flatProfiles rename rename_types) captures
    (fun _ => edgeType) (fun _ => num) admitted.val admitted.property.2 packetRead captureInput mappedInput
  have sourceClose : Capture.close captures (fun _ => edgeType) (fun _ => num)
      admitted.val admitted.property.2 packetRead captureInput = some closed := rfl
  have targetClose : Capture.close captures (fun _ => edgeType) (fun _ => num)
      (admitted.val.mapInstr rename.instr) (admitted.property.2.mapInstr (flatProfiles rename rename_types))
      (packetRead.mapInstr rename.instr) mappedInput = some closedMapped := rfl
  rw [sourceClose, targetClose] at h
  exact Option.some.inj h

private theorem ofCFG_congr {b e : Nat} {g h : LambdaSSA.FiniteCFG Opcode b e 0}
    {R : Fin b → Ty SortName} {D : Fin e → Ty SortName} (eq : g = h)
    (hg : g.HasType .nil R D) (hh : h.HasType .nil R D) :
    Program.ofCFG hg = Program.ofCFG hh := by
  subst h
  rfl

-- The packer receives the actual table returned by the target closure run.
example : Program.ofCFG closedMapped.property.1 = (Program.ofCFG closed.property.1).map rename rename_types :=
  (ofCFG_congr closedMapped_eq _ _).trans (Program.ofCFG_mapInstr rename rename_types closed.property.1)

private def silent : LambdaSSA.FiniteCFG Opcode 1 1 0 :=
  ⟨.br 0 .unit, fun _ => .br 0 (.bv 0)⟩

private theorem silentTyped : silent.HasType .nil (fun _ => Ty.unit) (fun _ => num) :=
  ⟨.br .unit, fun _ => .br .bv⟩

private theorem silent_tree (raw : Primitive Event Opcode Runtime) :
    region raw ambient (packedExecutionRegion silentTyped) = diverge := by
  rw [packedExecution_tree]
  have h : region raw ambient silent.erase = diverge := by
    simp only [silent, LambdaSSA.FiniteCFG.erase, LambdaSSA.Flat.erase, Morphism.CaseSSA.erase,
      region, LambdaSSA.Semantics.Interaction.term, pure_bind]
    exact iterate_pure_loop (fun p : BlockInput Runtime 1 => (0, p.2)) (0, .unit)
  rw [h, diverge_bind]

private def reduct := model.reduct rename rename_types rename_bottom

private theorem reduct_packet :
    LambdaSSA.Semantics.Interaction.term reduct.raw ambient (Morphism.CaseSSA.erase packetRead) =
      (captureProducer >>= fun reply => pure (Capture.packEnv 1 (env reply.down))) :=
  capture_packet

private theorem reduct_entry (capture : Nat) :
    region reduct.raw (env capture) admitted.val.entry.erase =
      vis (.call .tick capture) (fun reply => pure (0, packet reply)) := by
  change region reduct.raw (env capture)
    (.let₁ (.op .seed (.var 0)) (.br 0 (.pair (.var 0) .unit))) = _
  simp only [region, LambdaSSA.Semantics.Interaction.term, pure_bind, vis_bind, env, reduct,
    LambdaSSA.Semantics.Interaction.Typed.Ordered.Model.reduct, model, rename, instr, LambdaSSA.Semantics.extend_zero, packet, atom]

private theorem reduct_steps (capture : Nat) :
    (fun p : BlockInput Runtime 2 =>
      region reduct.raw (extend (env capture) p.2) (admitted.val.block p.1).erase >>=
        fun out => pure (splitTransfer 2 out)) = openStep capture := by
  funext p
  have block (i : Fin 2) :
      region reduct.raw (extend (env capture) p.2) (admitted.val.block i).erase =
        region instr (extend (env capture) p.2) (admitted.val.block i).erase := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl
  exact congrArg (fun t => t >>= fun out => pure (splitTransfer 2 out)) (block p.1)

private def cycleTrace : Trace Event (Transfer Runtime) :=
  .exchange .capture 7 (.exchange (.call .tick 7) 3 (.exchange (.call .tick 3) 5
    (.request (.call .tick 5))))

-- The captured value reaches the mapped seed request. A reply to the first
-- tick in the back-edge block then determines the next tick request.
private theorem captured_cycle :
    HasTrace (region reduct.raw ambient (packedExecutionRegion closed.property.1)) cycleTrace := by
  rw [packedExecution_tree, Capture.graph_tree reduct.raw closed.property.2 reduct_packet]
  simp only [captureProducer, vis_bind, pure_bind, cycleTrace, hasTrace_vis_exchange_iff]
  change HasTrace ((region reduct.raw (env 7) admitted.val.entry.erase >>= fun out =>
    Sum.elim pure (iter (fun p : BlockInput Runtime 2 =>
      region reduct.raw (extend (env 7) p.2) (admitted.val.block p.1).erase >>=
        fun out => pure (splitTransfer 2 out))) (splitTransfer 2 out)) >>= _) _
  rw [reduct_steps 7, reduct_entry 7]
  simp only [vis_bind, pure_bind, hasTrace_vis_exchange_iff]
  change HasTrace (iter (openStep 7) (0, packet 3) >>= _) _
  rw [tick_loop, vis_bind]
  simp only [hasTrace_vis_exchange_iff]
  rw [tick_loop, vis_bind]
  exact hasTrace_vis_request _ _

private theorem reduct_comparisons :
    reduct.Satisfies (Program.ofCFG silentTyped) (Program.ofCFG closed.property.1) ∧
    ¬ reduct.Satisfies (Program.ofCFG closed.property.1) (Program.ofCFG silentTyped) := by
  rw [satisfies_ofCFG_iff reduct silentTyped closed.property.1 ambient,
    satisfies_ofCFG_iff reduct closed.property.1 silentTyped ambient, silent_tree]
  refine ⟨traceLE_diverge _, fun h => ?_⟩
  have pending := h cycleTrace captured_cycle
  simp [cycleTrace, hasTrace_diverge_iff] at pending

-- A silent self-loop refines the effectful cycle, strictly, after both
-- tables have been relabelled and the mapped capture has been closed.
example :
    model.Satisfies (Program.ofCFG (silentTyped.mapInstr (flatProfiles rename rename_types)))
      (Program.ofCFG closedMapped.property.1) ∧
    ¬ model.Satisfies (Program.ofCFG closedMapped.property.1)
      (Program.ofCFG (silentTyped.mapInstr (flatProfiles rename rename_types))) := by
  rw [ofCFG_congr closedMapped_eq closedMapped.property.1
      (closed.property.1.mapInstr (flatProfiles rename rename_types))]
  rw [satisfies_ofCFG_map_iff model rename rename_types rename_bottom silentTyped closed.property.1,
    satisfies_ofCFG_map_iff model rename rename_types rename_bottom closed.property.1 silentTyped]
  change reduct.Satisfies (Program.ofCFG silentTyped) (Program.ofCFG closed.property.1) ∧
    ¬ reduct.Satisfies (Program.ofCFG closed.property.1) (Program.ofCFG silentTyped)
  exact reduct_comparisons

/-! ## The same comparison as an institutional sentence -/

open CategoryTheory

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Opcode

private def relabel : signature ⟶ signature :=
  ⟨rename, rename_types, rename_bottom⟩

private def comparison : FlatInstitution.Sentence signature :=
  ⟨1, fun _ => num, FlatInstitution.Table.ofTyped silentTyped,
    FlatInstitution.Table.ofTyped closed.property.1⟩

private def converse : FlatInstitution.Sentence signature :=
  ⟨comparison.exits, comparison.external, comparison.right, comparison.left⟩

private abbrev comparisonCorridor :=
  (FlatInstitution.institution.{0, 0} Event SortName).I.map relabel

-- Sentence translation agrees with the actual relabelled executable closure.
example : (comparisonCorridor.sen comparison).right.code = closedMapped.val :=
  closedMapped_eq.symm

-- Test the bundled institution's satisfaction field in both directions.
example :
    (FlatInstitution.room Event signature).Sat (Discrete.mk model) (comparisonCorridor.sen comparison) ∧
    ¬ (FlatInstitution.room Event signature).Sat (Discrete.mk model) (comparisonCorridor.sen converse) :=
  ⟨(comparisonCorridor.sat (Discrete.mk model) comparison).mpr reduct_comparisons.1,
    fun h => reduct_comparisons.2 ((comparisonCorridor.sat (Discrete.mk model) converse).mp h)⟩

/-! ## Packing the cyclic comparison into the ordered singleton institution -/

private abbrev packing := PackedInstitution.packingComorphism.{0, 0} Event SortName

-- The packed side of the comorphism's naturality square uses the actual
-- representative obtained by packing the relabelled closure.
example : (packing.ρ.app signature ≫ (PackedInstitution.institution.{0, 0} Event SortName).I.map
      relabel).sen comparison =
    ⟨1, fun _ => num, Program.ofCFG (silentTyped.mapInstr (flatProfiles rename rename_types)),
      Program.ofCFG closedMapped.property.1⟩ := by
  have naturality := congrArg (fun c => c.sen comparison) (packing.ρ.naturality relabel)
  exact naturality.symm.trans
    (congrArg (PackedInstitution.Sentence.mk 1 (fun _ => num) _)
      (ofCFG_congr closedMapped_eq.symm _ _))

-- Apply the comorphism's satisfaction law after the noninjective relabelling.
example :
    (PackedInstitution.room Event signature).Sat (Discrete.mk model)
      ((packing.ρ.app signature).sen (comparisonCorridor.sen comparison)) ∧
    ¬ (PackedInstitution.room Event signature).Sat (Discrete.mk model)
      ((packing.ρ.app signature).sen (comparisonCorridor.sen converse)) :=
  ⟨(packing.satisfaction signature (Discrete.mk model) _).mpr
      ((comparisonCorridor.sat (Discrete.mk model) comparison).mpr reduct_comparisons.1),
    fun h => reduct_comparisons.2 ((comparisonCorridor.sat (Discrete.mk model) converse).mp
      ((packing.satisfaction signature (Discrete.mk model) _).mp h))⟩

end Silmaril.Isotope.Bridge.NamedFlat.Interaction.Examples
