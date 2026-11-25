module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Defs

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs

open Execution.Runtime (FuncAddr Value)

theorem lookup_table (program : Program) (address : FuncAddr) :
    program.table.lookup address = (program.lookup address).map Function.entry := by
  unfold Table.lookup Program.table Program.lookup
  rw [List.getElem?_map]
  cases program.functions[address.value]? with
  | none => rfl
  | some slot => cases slot <;> rfl

theorem target_resolved {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {target : CallTarget}
    (found : program.lookup address = some fn) (used : target ∈ fn.targets) :
    program.order target.address address :=
  Table.resolved_of_target (Program.rankCheck checked)
    ⟨fn.rank, by rw [lookup_table, found]; rfl⟩ used

private theorem map_child_smaller {fn : Function} {r₁ r₂ : CallTarget → Phase → Phase → Prop} {a b : Phase} {kind : LabelKind}
    (map : ∀ target ∈ fn.targets, ∀ {c d}, sizeOf c < sizeOf a → r₁ target c d → r₂ target c d)
    (step : Layer fn r₁ a b kind) : Layer fn r₂ a b kind := by
  induction step with
  | resolve args => exact .resolve args
  | enter args typed => exact .enter args typed
  | numeric step => exact .numeric step
  | localSet write => exact .localSet write
  | localTee write => exact .localTee write
  | ifSelect locals saved condition result thenBody elseBody rest =>
    exact .ifSelect locals saved condition result thenBody elseBody rest
  | indexedIfSelect locals operands condition index signature thenBody elseBody rest =>
    exact .indexedIfSelect locals operands condition index signature thenBody elseBody rest
  | blockEnter locals saved result body rest => exact .blockEnter locals saved result body rest
  | @blockStep kind locals saved result rest inner next step ih =>
    exact .blockStep saved result rest (ih (fun target used {_ _} smaller branch =>
      map target used (Nat.lt_trans smaller (by simp [Phase.label.sizeOf_spec, Body.block.sizeOf_spec]; omega)) branch))
  | indexedBlockEnter locals saved args index signature body rest resolved typed =>
    exact .indexedBlockEnter locals saved args index signature body rest resolved typed
  | @indexedBlockStep kind locals inner next saved signature rest step ih =>
    exact .indexedBlockStep saved signature rest (ih (fun target used {_ _} smaller branch =>
      map target used (Nat.lt_trans smaller (by simp [Phase.label.sizeOf_spec, Body.indexedBlock.sizeOf_spec]; omega)) branch))
  | loopEnter locals saved result body rest => exact .loopEnter locals saved result body rest
  | @loopStep kind locals inner next saved result original rest step ih =>
    exact .loopStep saved result original rest (ih (fun target used {_ _} smaller branch =>
      map target used (Nat.lt_trans smaller (by simp [Phase.label.sizeOf_spec, Body.loop.sizeOf_spec]; omega)) branch))
  | indexedLoopEnter locals saved args index signature body rest resolved typed =>
    exact .indexedLoopEnter locals saved args index signature body rest resolved typed
  | @indexedLoopStep kind locals inner next saved index signature original rest step ih =>
    exact .indexedLoopStep saved index signature original rest (ih (fun target used {_ _} smaller branch =>
      map target used (Nat.lt_trans smaller (by simp [Phase.label.sizeOf_spec, Body.indexedLoop.sizeOf_spec]; omega)) branch))
  | unreachable args stack rest => exact .unreachable args stack rest
  | dispatch locals saved operands target rest used count => exact .dispatch locals saved operands target rest used count
  | child locals saved target rest used live step =>
    exact .child locals saved target rest used live (map target used
      (by simp [Phase.label.sizeOf_spec, Body.active.sizeOf_spec]; omega) step)
  | discard step => exact .discard step
  | branchIf locals stack condition depth result rest => exact .branchIf locals stack condition depth result rest
  | branchTable locals stack selector depths fallback result rest =>
    exact .branchTable locals stack selector depths fallback result rest
  | branchHere locals extra values result rest arity => exact .branchHere locals extra values result rest arity
  | branchOuter locals stack depth result rest outer => exact .branchOuter locals stack depth result rest outer
  | returnLabel locals stack rest => exact .returnLabel locals stack rest
  | returnFrame locals extra results arity => exact .returnFrame locals extra results arity
  | leaveValues args stack => exact .leaveValues args stack
  | leaveTrap args => exact .leaveTrap args
  | leaveFrame args result typed => exact .leaveFrame args result typed

theorem map_child {fn : Function} {r₁ r₂ : CallTarget → Phase → Phase → Prop} {a b : Phase} {kind : LabelKind}
    (map : ∀ target ∈ fn.targets, ∀ {c d}, r₁ target c d → r₂ target c d)
    (step : Layer fn r₁ a b kind) : Layer fn r₂ a b kind :=
  map_child_smaller (fun target used {_ _} _ => map target used) step

private theorem unfold_edge {program : Program} (checked : program.check = true) (address : FuncAddr) (a b : Phase) (kind : LabelKind) :
    program.EdgeAt checked address kind a b ↔
      ∃ fn, program.lookup address = some fn ∧
        Layer fn (fun target c d => ∃ _ : program.order target.address address,
          program.Edge checked target.address c d) a b kind := by
  conv_lhs =>
    unfold Program.EdgeAt
    rw [WellFounded.fix_eq]
  rfl

theorem edge_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} {a b : Phase} {kind : LabelKind} (found : program.lookup address = some fn) :
    program.EdgeAt checked address kind a b ↔
      Layer fn (fun target => program.Edge checked target.address) a b kind := by
  rw [unfold_edge checked]
  constructor
  · rintro ⟨current, lookup, step⟩
    have same := Option.some.inj (lookup.symm.trans found)
    subst current
    exact map_child (fun _ _ _ _ ⟨_, edge⟩ => edge) step
  · intro step
    exact ⟨fn, found, map_child (fun _ used _ _ edge => ⟨target_resolved checked found used, edge⟩) step⟩

theorem unfold_frame_edge {program : Program} {address : FuncAddr} {a b : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind a b ↔
      ∃ fn, program.lookup address = some fn ∧
        Layer fn (fun target c d => ∃ _ : sizeOf c < sizeOf a,
          program.FrameEdge target.address c d) a b kind := by
  conv_lhs => unfold Program.FrameEdgeAt; rw [WellFounded.fix_eq]
  rfl

theorem frame_edge_iff {program : Program} {address : FuncAddr} {fn : Function} {a b : Phase} {kind : LabelKind}
    (found : program.lookup address = some fn) :
    program.FrameEdgeAt address kind a b ↔
      Layer fn (fun target => program.FrameEdge target.address) a b kind := by
  rw [unfold_frame_edge]
  constructor
  · rintro ⟨_, lookup, step⟩
    cases Option.some.inj (lookup.symm.trans found)
    exact map_child (fun _ _ _ _ ⟨_, child⟩ => child) step
  · intro step
    exact ⟨fn, found, map_child_smaller (fun _ _ {_ _} smaller child => ⟨smaller, child⟩) step⟩

theorem frame_edge_iff_ranked {program : Program} (checked : program.check = true) (address : FuncAddr) :
    ∀ {a b kind}, program.FrameEdgeAt address kind a b ↔ program.EdgeAt checked address kind a b := by
  induction address using (program.table.wellFounded (Program.rankCheck checked)).induction with
  | h address ih =>
    intro a b kind
    cases found : program.lookup address with
    | none => rw [unfold_frame_edge, unfold_edge]; simp [found]
    | some fn =>
      rw [frame_edge_iff found, edge_iff checked found]
      constructor <;> intro step
      · exact map_child (fun target used _ _ move => (ih target.address (target_resolved checked found used)).mp move) step
      · exact map_child (fun target used _ _ move => (ih target.address (target_resolved checked found used)).mpr move) step

theorem label_outcome {fn : Function} {childStep : CallTarget → Phase → Phase → Prop}
    {a b : Phase} {kind : LabelKind} (step : Layer fn childStep a b kind) :
    (∃ locals inner, a = .label locals inner) → b.LabelOutcome := by
  induction step with
  | @blockStep kind locals saved result rest inner next step ih =>
    intro _
    have valid := ih ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.afterBlock, Phase.LabelOutcome]
    case exit result => cases result <;> trivial
  | @indexedBlockStep kind locals inner next saved signature rest step ih =>
    intro _
    have valid := ih ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.afterBlock, Phase.LabelOutcome]
    case exit result => cases result <;> trivial
  | @loopStep kind locals inner next saved result original rest step ih =>
    intro _
    have valid := ih ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.afterBlock, Phase.LabelOutcome]
    case exit result => cases result <;> trivial
  | @indexedLoopStep kind locals inner next saved index signature original rest step ih =>
    intro _
    have valid := ih ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.afterBlock, Phase.LabelOutcome]
    case exit result => cases result <;> trivial
  | @branchHere kind _ _ _ _ _ _ => cases kind <;> simp [LabelKind.branchHere, Phase.LabelOutcome]
  | _ => simp [Phase.LabelOutcome]

theorem frame_active_iff {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.FrameEdge target.address a out ∧ b = .label locals (Body.attach saved target rest out) := by
  rw [frame_edge_iff found]
  constructor
  · intro step
    cases step with
    | child _ _ _ _ _ _ step => exact ⟨_, step, rfl⟩
  · rintro ⟨out, step, rfl⟩
    exact .child locals saved target rest used live step

theorem active_iff {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} {b : Phase} {kind : LabelKind} :
    program.EdgeAt checked address kind (.label locals (.active saved target a rest)) b ↔
      ∃ out, program.Edge checked target.address a out ∧ b = .label locals (Body.attach saved target rest out) := by
  rw [← frame_edge_iff_ranked checked address, frame_active_iff found used live]
  simp only [Program.FrameEdge, Program.Edge, frame_edge_iff_ranked checked]

theorem block_iff {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {locals saved : List Value} {result : Option NumType} {inner : Body} {rest : List Op} {out : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind (.label locals (.block saved result inner rest)) out ↔
      ∃ next, program.FrameEdge address (.label locals inner) next ∧ out = next.afterBlock saved result rest := by
  rw [frame_edge_iff found]
  constructor
  · intro step
    cases step with
    | blockStep _ _ _ step => exact ⟨_, (frame_edge_iff found).mpr step, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact .blockStep saved result rest ((frame_edge_iff found).mp step)

theorem indexed_block_iff {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {locals saved : List Value} {signature : Wasm.V1.FuncType} {inner : Body} {rest : List Op}
    {out : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind (.label locals (.indexedBlock saved signature inner rest)) out ↔
      ∃ next, program.FrameEdgeAt address (.indexed signature) (.label locals inner) next ∧
        out = next.afterBlock saved none rest (.indexed signature) := by
  rw [frame_edge_iff found]
  constructor
  · intro step
    cases step with
    | indexedBlockStep _ _ _ step => exact ⟨_, (frame_edge_iff found).mpr step, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact .indexedBlockStep saved signature rest ((frame_edge_iff found).mp step)

theorem loop_iff {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {locals saved : List Value} {result : Option NumType} {inner : Body} {original rest : List Op}
    {out : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind (.label locals (.loop saved result original inner rest)) out ↔
      ∃ next, program.FrameEdgeAt address (.loop result original) (.label locals inner) next ∧
        out = next.afterBlock saved result rest (.loop result original) := by
  rw [frame_edge_iff found]
  constructor
  · intro step
    cases step with
    | loopStep _ _ _ _ step => exact ⟨_, (frame_edge_iff found).mpr step, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact .loopStep saved result original rest ((frame_edge_iff found).mp step)

theorem indexed_loop_iff {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {locals saved : List Value} {index : TypeIdx} {signature : Wasm.V1.FuncType} {inner : Body} {original rest : List Op}
    {out : Phase} {kind : LabelKind} :
    program.FrameEdgeAt address kind (.label locals (.indexedLoop saved index signature original inner rest)) out ↔
      ∃ next, program.FrameEdgeAt address (.indexedLoop index signature original) (.label locals inner) next ∧
        out = next.afterBlock saved none rest (.indexedLoop index signature original) := by
  rw [frame_edge_iff found]
  constructor
  · intro step
    cases step with
    | indexedLoopStep _ _ _ _ _ step => exact ⟨_, (frame_edge_iff found).mpr step, rfl⟩
  · rintro ⟨next, step, rfl⟩
    exact .indexedLoopStep saved index signature original rest ((frame_edge_iff found).mp step)

private theorem source_active {program : Program}
    {address : FuncAddr} {a b : Phase} (ready : ∀ args, a ≠ .call args)
    (edge : program.FrameEdge address a b) : a.Active := by
  obtain ⟨_, _, step⟩ := unfold_frame_edge.mp edge
  cases step with
  | resolve args => exact (ready args rfl).elim
  | _ => trivial

private theorem layer_not_call {fn : Function} {child : CallTarget → Phase → Phase → Prop} {a b : Phase}
    (step : Layer fn child a b) (args : List Value) : b ≠ .call args := by
  cases step with
  | @blockStep _ locals saved result rest inner next step =>
    have outcome := label_outcome step ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.LabelOutcome, Phase.afterBlock]
    case exit result => cases result <;> simp
  | @indexedBlockStep _ locals inner next saved signature rest step =>
    have outcome := label_outcome step ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.LabelOutcome, Phase.afterBlock]
    case exit result => cases result <;> simp
  | @loopStep _ locals inner next saved result original rest step =>
    have outcome := label_outcome step ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.LabelOutcome, Phase.afterBlock]
    case exit result => cases result <;> simp
  | @indexedLoopStep _ locals inner next saved index signature original rest step =>
    have outcome := label_outcome step ⟨_, _, rfl⟩
    cases next <;> simp_all [Phase.LabelOutcome, Phase.afterBlock]
    case exit result => cases result <;> simp
  | _ => simp [LabelKind.branchHere]

theorem frame_not_call {program : Program} {address : FuncAddr} {a b : Phase}
    (edge : program.FrameEdge address a b) (args : List Value) : b ≠ .call args := by
  obtain ⟨_, _, step⟩ := unfold_frame_edge.mp edge
  exact layer_not_call step args

theorem frame_lift_child {program : Program}
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a b : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} (run : program.FrameRuns target.address a b) :
    program.FrameRuns address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) := by
  have noCall (operands : List Value) : a ≠ .call operands := by
    intro eq
    subst a
    exact live
  have first : Body.attach saved target rest a = .active saved target a rest := by
    cases a <;> simp_all [Body.attach, Phase.Active]
  rw [← first]
  induction run with
  | refl => exact .refl
  | @tail q r before step ih =>
    have notAtCall (operands : List Value) : q ≠ .call operands := by
      cases before with
      | refl => exact noCall operands
      | tail _ edge => exact frame_not_call edge operands
    have active := source_active notAtCall step
    have attach : Body.attach saved target rest q = .active saved target q rest := by
      cases q <;> simp_all [Body.attach, Phase.Active]
    apply ih.tail
    rw [attach]
    exact (frame_active_iff found used active).mpr ⟨r, step, rfl⟩

theorem lift_child {program : Program} (checked : program.check = true)
    {address : FuncAddr} {fn : Function} (found : program.lookup address = some fn)
    {target : CallTarget} (used : target ∈ fn.targets) {a b : Phase} (live : a.Active)
    {locals saved : List Value} {rest : List Op} (run : program.Runs checked target.address a b) :
    program.Runs checked address (.label locals (.active saved target a rest))
      (.label locals (Body.attach saved target rest b)) := by
  have toFrame := Relation.ReflTransGen.mono
    (fun _ _ edge => (frame_edge_iff_ranked checked target.address).mpr edge) _ _ run
  exact Relation.ReflTransGen.mono (fun _ _ edge => (frame_edge_iff_ranked checked address).mp edge)
    _ _ (frame_lift_child found used live toFrame)

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Proofs
