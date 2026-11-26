module

public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.CFG.Proofs

open RVSDG (Port Tuple Origin Wires Locals)
open Diamond (Ty ValueSort Signature Model Val dataPorts)
open Join (Block)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {n : Nat}
variable {m : Model.{u, v, w} Op}

private theorem get_tabulate {T : Type u} {F : T → Type w} {ts : List T} {t : T}
    (p : Port ts t) (f : ∀ {s}, Port ts s → F s) :
    (tabulate ts f).get p = f p := by
  induction p with
  | head => rfl
  | tail _ ih => exact ih (fun q => f (.tail q))

private theorem get_map {T : Type u} {F : T → Type v} {G : T → Type w}
    {ts : List T} {t : T} (p : Port ts t) (xs : Tuple F ts) (f : ∀ s, F s → G s) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs; exact ih _

private theorem readBank_eq {T : Type u} {F : T → Type w} {ts : List T} (bank : Tuple F ts)
    (lookup : ∀ {t}, Port ts t → Option (F t))
    (h : ∀ {t} (p : Port ts t), lookup p = some (bank.get p)) :
    readBank ts lookup = some bank := by
  induction bank with
  | nil => rfl
  | cons head tail ih =>
    change (match lookup .head with
      | none => none
      | some value => (readBank _ (fun p => lookup (.tail p))).map (Tuple.cons value)) =
        some (.cons head tail)
    rw [h .head, ih (fun p => lookup (.tail p)) (fun p => h (.tail p))]
    rfl

private theorem write_output_arg {args : List (Ty Data)} {past : List (List (Ty Data))}
    {ts : List (Ty Data)} {s t : Ty Data} (dest : Port ts s)
    (i : Fin past.length) (out : Port past[i] s) (current : Wires args past ts)
    (p : Port ts t) (a : Port args t)
    (h : (write dest (.output i out) current).get p = .arg a) :
    current.get p = .arg a := by
  induction dest generalizing t with
  | head => cases p <;> cases current <;> simp_all [write, Tuple.get]
  | tail dest ih =>
    cases p <;> cases current
    · exact h
    · exact ih _ _ _ _ h

private theorem version_arg {args : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (current : Wires args past (dataPorts regs))
    {t : Ty Data} (p : Port (dataPorts regs) t) (a : Port args t)
    (h : (block.versions current).get p = .arg a) : current.get p = .arg a := by
  induction block generalizing past with
  | nil => exact h
  | cons quad rest ih =>
    have after := ih (rebind current quad.dest) h
    unfold rebind at after
    have before := write_output_arg _ _ _ _ p a after
    rw [get_map] at before
    cases hp : current.get p <;> simp_all [keep]

private theorem compiled_outgoing {args : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (current : Wires args past (dataPorts regs)) :
    (compileBlock block current).outgoing = block.versions current := by
  induction block generalizing past with
  | nil => rfl
  | cons quad rest ih => exact ih (rebind current quad.dest)

theorem compiled_read {args : List (Ty Data)} {past : List (List (Ty Data))}
    (block : Block Op regs) (m : Model.{u, v, w} Op)
    (entry : Tuple (Val m.value) args) (locals : Locals (Val m.value) past)
    (current : Wires args past (dataPorts regs)) :
    (compileBlock block current).outgoing.read entry
        ((compileBlock block current).flow.eval m entry locals) =
      block.eval m (current.read entry locals) := by
  induction block generalizing past with
  | nil => rfl
  | cons quad rest ih =>
    let produced := Tuple.cons (F := Val m.value) (t := .value quad.result)
      (m.run quad.op ((quad.inputWires current).read entry locals)) .nil
    exact (ih (locals.snoc produced) (rebind current quad.dest)).trans
      (congrArg (Block.eval rest m) (quad.step_read m entry locals current))

private theorem header_get {t : Ty Data} (prior : Graph Op regs n) (preds : Predecessors n)
    (p : Port (dataPorts regs) t) :
    (prior.header preds).get p =
      if preds.rest.any (fun pred => (prior.versions pred).get p !=
          (prior.versions preds.first).get p) then none else some ((prior.versions preds.first).get p) :=
  get_tabulate p _

theorem header_phi_iff {t : Ty Data} (prior : Graph Op regs n) (preds : Predecessors n)
    (p : Port (dataPorts regs) t) :
    (prior.header preds).get p = none ↔
      ∃ pred ∈ preds.rest, (prior.versions pred).get p ≠ (prior.versions preds.first).get p := by
  rw [header_get]
  split <;> rename_i h
  · simpa using h
  · simpa using h

theorem selected_version {t : Ty Data} (prior : Graph Op regs n) (preds : Predecessors n)
    (edge : Fin (preds.rest.length + 1)) (p : Port (dataPorts regs) t)
    (version : Version n) (h : (prior.header preds).get p = some version) :
    (prior.column preds edge).get p = version := by
  rw [header_get] at h
  split at h <;> rename_i prev
  · contradiction
  · injection h with h
    subst version
    refine Fin.cases rfl (fun slot => ?_) edge
    change (prior.versions (preds.rest.get slot)).get p = (prior.versions preds.first).get p
    by_cases agrees : (prior.versions (preds.rest.get slot)).get p =
        (prior.versions preds.first).get p
    · exact agrees
    · exact False.elim (prev (List.any_eq_true.mpr
        ⟨_, List.get_mem _ slot, by simpa using agrees⟩))

theorem header_read (prior : Graph Op regs n) (preds : Predecessors n)
    (edge : Fin (preds.rest.length + 1)) (older : Values m regs n)
    {t : Ty Data} (p : Port (dataPorts regs) t) :
    (prior.header preds).read older (older.read (prior.column preds edge)) p =
      older.read (prior.column preds edge) p := by
  unfold Inputs.read
  split
  · rfl
  · rename_i version h
    exact congrArg (fun key => older key p) (selected_version prior preds edge p version h).symm

private theorem push_lift (older : Values m regs n) (phis : Slots m regs)
    (writes : Nat → Slots m regs) (version : Version n) {t : Ty Data} (p : Port (dataPorts regs) t) :
    older.push phis writes version.lift p = older version p := by
  cases version <;> simp [Version.lift, Values.push]

private theorem push_input (older : Values m regs n) (phis : Slots m regs)
    (writes : Nat → Slots m regs) (header : Inputs regs n)
    {t : Ty Data} (p : Port (dataPorts regs) t) :
    older.push (header.phiValues phis) writes (Inputs.version (header.get p)) p = header.read older phis p := by
  cases h : header.get p with
  | none => simp [h, Inputs.version, Inputs.read, Inputs.phiValues, Values.push]
  | some version => simp [h, Inputs.version, Inputs.read, push_lift]

private theorem record_reads (block : Block Op regs) (m : Model.{u, v, w} Op)
    (header : Inputs regs n) (older : Values m regs n) (phis : Slots m regs) (bank : Bank m regs)
    (ready : ∀ {t} (p : Port (dataPorts regs) t), header.read older phis p = some (bank.get p)) :
    ∃ values, record block m header older phis = some values ∧
      ∀ {t} (p : Port (dataPorts regs) t), values.read (outgoing block header) p =
        some ((block.eval m bank).get p) := by
  let flow := (compileBlock block (initial regs)).flow
  let locals := flow.eval m bank PUnit.unit
  let writes := writeValues block m bank locals
  refine ⟨older.push (header.phiValues phis) writes, ?_, ?_⟩
  · unfold record
    rw [readBank_eq bank _ ready]
    rfl
  · intro t p
    have readLocal : (localVersions block).read bank locals = block.eval m bank := by
      unfold localVersions
      rw [← compiled_outgoing]
      exact (compiled_read (past := []) block m bank PUnit.unit (initial regs)).trans
        (congrArg (block.eval m) (read_initial m bank))
    have atPort := (read_get m (localVersions block) bank locals p).symm.trans
      (congrArg (fun bs => bs.get p) readLocal)
    unfold Values.read outgoing
    rw [get_map]
    cases h : (localVersions block).get p with
    | arg arg =>
      change older.push (header.phiValues phis) writes (Inputs.version (header.get arg)) p = _
      have same := version_arg block (initial regs) p arg h
      rw [initial_get] at same
      cases same
      rw [push_input, ready p]
      rw [h] at atPort
      exact congrArg some atPort
    | output j out =>
      rw [h] at atPort
      simp [Values.push, writes, writeValues, h, atPort]

theorem path_reads {graph : Graph Op regs n} {i : Fin n}
    (path : Path graph i) (m : Model.{u, v, w} Op) (input : Bank m regs) :
    ∃ values, path.values m input = some values ∧
      ∀ {t} (p : Port (dataPorts regs) t), values.read (graph.versions i) p =
        some ((path.eval m input).get p) := by
  induction path with
  | entry =>
    apply record_reads
    intro t p
    unfold Inputs.read entryInputs
    rw [get_tabulate]
  | earlier path ih =>
    obtain ⟨older, hvals, hold⟩ := ih
    refine ⟨older.push (fun {_} _ => none) (fun _ {_} _ => none), ?_, ?_⟩
    · simp [Path.values, hvals]
    · intro t p
      simpa [Graph.versions, Values.read, get_map, push_lift, Path.eval] using hold p
  | @edge _ prior preds body edge path ih =>
    obtain ⟨older, hvals, hold⟩ := ih
    obtain ⟨values, hrecord, hread⟩ := record_reads body m (prior.header preds) older
      (older.read (prior.column preds edge)) (path.eval m input)
      (fun p => (header_read prior preds edge older p).trans (hold p))
    refine ⟨values, ?_, ?_⟩
    · simpa [Path.values, hvals] using hrecord
    · intro t p
      simpa [Graph.versions, Path.eval, Graph.header] using hread p

theorem path_bank {graph : Graph Op regs n} {i : Fin n} (path : Path graph i)
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    ∃ values, path.values m input = some values ∧
      readBank (dataPorts regs) (values.read (graph.versions i)) = some (path.eval m input) := by
  obtain ⟨values, defined, agrees⟩ := path_reads path m input
  exact ⟨values, defined, readBank_eq _ _ (fun p => agrees p)⟩

theorem edge_bank (prior : Graph Op regs n) (preds : Predecessors n)
    (occurrence : Fin (preds.rest.length + 1)) (path : Path prior (preds.get occurrence))
    (m : Model.{u, v, w} Op) (input : Bank m regs) :
    ∃ values, path.values m input = some values ∧
      readBank (dataPorts regs) (values.read (prior.column preds occurrence)) =
        some (path.eval m input) ∧
      readBank (dataPorts regs) ((prior.header preds).read values
        (values.read (prior.column preds occurrence))) = some (path.eval m input) := by
  obtain ⟨values, defined, agrees⟩ := path_reads path m input
  refine ⟨values, defined, readBank_eq _ _ (fun p => agrees p), readBank_eq _ _ ?_⟩
  intro t p
  exact (header_read prior preds occurrence values p).trans (agrees p)

end Silmaril.SSA.SeaOfNodes.Quads.CFG.Proofs
