module

public import Silmaril.SSA.Peggy.FieldHeap.Linearize.Defs
public import Silmaril.SSA.PEG.Semantics.Thms

public section

namespace Silmaril.SSA.Peggy.FieldHeap.Linearize.Proofs

open RVSDG (Port Tuple)
open Silmaril.Semantics.Operational (Environment)

variable {params : List (PEG.Ty DataSort)} {reads nodes : Nat}
variable {g : Graph params reads nodes} {t : PEG.Ty DataSort}

private def evaluated (values : g.Valuation interpretation) (i : PEG.Index 0)
    (r : PEG.Ref g.sort t) : Option (interpretation.Value t) :=
  r.read interpretation.carrier (values (r.id, i))

private def evalRow {sort : Fin nodes → PEG.Ty DataSort} (input : Inputs params)
    (read : {t : PEG.Ty DataSort} → PEG.Ref sort t → Option (interpretation.Value t)) :
    {t : PEG.Ty DataSort} → Row params sort t → Option (interpretation.Value t)
  | _, .param p => some (input.get p)
  | _, .store f s r v =>
    (read s).bind fun state => (read r).bind fun receiver =>
      (read v).map (setField state receiver f)
  | _, .load f s r =>
    (read s).bind fun state => (read r).map fun receiver => getField state receiver f
  | _, .readState result => (read result).map ReadResult.state
  | _, .readValue result => (read result).map ReadResult.value

private def collectCons {ty : PEG.Ty DataSort} {ts : List (PEG.Ty DataSort)}
    (value : Option (interpretation.Value ty)) (rest : Option (Tuple interpretation.Value ts)) :
    Option (Tuple interpretation.Value (ty :: ts)) :=
  match value, rest with
  | some value, some rest => some (.cons value rest)
  | _, _ => none

private def collectRefs {sort : Fin nodes → PEG.Ty DataSort}
    (read : {ty : PEG.Ty DataSort} → PEG.Ref sort ty → Option (interpretation.Value ty)) :
    {ts : List (PEG.Ty DataSort)} → Tuple (PEG.Ref sort) ts → Option (Tuple interpretation.Value ts)
  | _, .nil => some .nil
  | _, .cons ref refs => collectCons (read ref) (collectRefs read refs)

private theorem collectRefs_eq {sort : Fin nodes → PEG.Ty DataSort}
    (read : {ty : PEG.Ty DataSort} → PEG.Ref sort ty → Option (interpretation.Value ty))
    {ts : List (PEG.Ty DataSort)} (args : Tuple (PEG.Ref sort) ts) :
    PEG.collect ts (fun pos => read (args.get (PEG.portAt ts pos))) = collectRefs read args := by
  induction args with
  | nil => rfl
  | @cons ty ts ref rest ih =>
    let args := Tuple.cons ref rest
    have head : args.get (PEG.portAt (ty :: ts) 0) = ref := rfl
    have tail (j : Fin ts.length) :
        args.get (PEG.portAt (ty :: ts) j.succ) = rest.get (PEG.portAt ts j) := rfl
    have remaining : (fun j : Fin ts.length => read (args.get (PEG.portAt (ty :: ts) j.succ))) =
        (fun j : Fin ts.length => read (rest.get (PEG.portAt ts j))) :=
      funext fun j => congrArg read (tail j)
    simp only [PEG.collect, show args = Tuple.cons ref rest from rfl] at head remaining ⊢
    rw [head, remaining, ih]
    simp only [collectRefs, collectCons]
    cases eq : read ref with
    | none => erw [eq]
    | some _ =>
      erw [eq]
      cases collectRefs read rest <;> rfl

private theorem node_eq {sort : Fin nodes → PEG.Ty DataSort}
    (node : PEG.Node Op params (Fin 0) sort t) (input : Inputs params) (i : PEG.Index 0)
    (read : {ty : PEG.Ty DataSort} → PEG.Index 0 → PEG.Ref sort ty → Option (interpretation.Value ty))
    {description : Row params sort t} (described : Row.ofNode node = some description) :
    node.label.interpret interpretation input i (fun p j _ => read j (node.arg p)) =
      evalRow input (read i) description := by
  obtain ⟨_, label, args⟩ := node
  cases label with
  | param slot =>
    change some (.param slot) = some description at described
    cases described
    rfl
  | op instr =>
    cases instr with
    | setField f =>
      cases args
      rename_i s rest
      cases rest
      rename_i r rest
      cases rest
      rename_i v rest
      cases rest
      change some (.store f s r v) = some description at described
      injection described with eq
      subst description
      refine (congrArg (fun args => args.elim none (interpretation.run (.setField f)))
        (collectRefs_eq (read i) (.cons s (.cons r (.cons v .nil))))).trans ?_
      simp only [collectRefs, evalRow]
      cases read i s <;> cases read i r <;> cases read i v <;> rfl
    | getField f =>
      cases args
      rename_i s rest
      cases rest
      rename_i r rest
      cases rest
      change some (.load f s r) = some description at described
      injection described with eq
      subst description
      refine (congrArg (fun args => args.elim none (interpretation.run (.getField f)))
        (collectRefs_eq (read i) (.cons s (.cons r .nil)))).trans ?_
      simp only [collectRefs, evalRow]
      cases read i s <;> cases read i r <;> rfl
    | readState =>
      cases args
      rename_i result rest
      cases rest
      change some (.readState result) = some description at described
      injection described with eq
      subst description
      cases hr : read i result <;>
        simp [PEG.Label.interpret, PEG.Node.arg, PEG.portAt, PEG.collect, Tuple.get, evalRow, hr] <;> rfl
    | readValue =>
      cases args
      rename_i result rest
      cases rest
      change some (.readValue result) = some description at described
      injection described with eq
      subst description
      cases hr : read i result <;>
        simp [PEG.Label.interpret, PEG.Node.arg, PEG.portAt, PEG.collect, Tuple.get, evalRow, hr] <;> rfl
    | forwardRead => cases described
  | phi => cases described
  | theta loop | eval loop | pass loop => exact loop.elim0

private theorem row_eq {input : Inputs params} {values : g.Valuation interpretation}
    (solves : g.Solves interpretation input values) (i : PEG.Index 0)
    (r : PEG.Ref g.sort t) {description : Row params g.sort t}
    (described : row g r = some description) :
    evaluated values i r = evalRow input (evaluated values i) description := by
  obtain ⟨id, typed⟩ := r
  cases typed
  change values (id, i) = _
  rw [solves (id, i)]
  exact node_eq (g.node id) input i (fun j => evaluated values j) described

private theorem parameter_eq {input : Inputs params} {values : g.Valuation interpretation}
    (solves : g.Solves interpretation input values) (i : PEG.Index 0)
    (r : PEG.Ref g.sort t) (slot : Port params t) (found : parameter g r = some slot) :
    evaluated values i r = some (input.get slot) := by
  unfold parameter at found
  split at found <;> try contradiction
  rename_i actual described
  cases found
  exact row_eq solves i r described

private theorem trace_eq {input : Inputs params} {values : g.Valuation interpretation}
    (solves : g.Solves interpretation input values) (i : PEG.Index 0)
    (fuel : Nat) (token : PEG.Ref g.sort stateTy) (schedule : Schedule params nodes)
    (found : trace g fuel token = some schedule) :
    evaluated values i token = some (schedule.run input).state ∧
      ∀ (r : PEG.Ref g.sort readTy), schedule.hasLoad r.id = true →
        (evaluated values i r).map ReadResult.value = (schedule.run input).loads r.id := by
  induction fuel generalizing token schedule with
  | zero => cases found
  | succ fuel ih =>
    simp only [trace] at found
    split at found
    · rename_i slot tokenRow
      cases found
      exact ⟨row_eq solves i token tokenRow, fun _ h => by cases h⟩
    · rename_i field s r v tokenRow
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
      obtain ⟨prior, traced, receiver, receiverSlot, value, valueSlot, rfl⟩ := found
      obtain ⟨stateEq, loadsEq⟩ := ih s prior traced
      refine ⟨?_, loadsEq⟩
      rw [row_eq solves i token tokenRow]
      change (evaluated values i s).bind (fun state =>
        (evaluated values i r).bind fun receiver => (evaluated values i v).map (setField state receiver field)) = _
      rw [stateEq, parameter_eq solves i r receiver receiverSlot, parameter_eq solves i v value valueSlot]
      rfl
    · rename_i result tokenRow
      split at found
      · rename_i field s r loadRow
        simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
        obtain ⟨prior, traced, receiver, receiverSlot, rfl⟩ := found
        obtain ⟨stateEq, loadsEq⟩ := ih s prior traced
        have loadEq : evaluated values i result =
            some (getField (prior.run input).state (input.get receiver) field) := by
          rw [row_eq solves i result loadRow]
          change (evaluated values i s).bind (fun state =>
            (evaluated values i r).map fun receiver => getField state receiver field) = _
          rw [stateEq, parameter_eq solves i r receiver receiverSlot]
          rfl
        constructor
        · rw [row_eq solves i token tokenRow]
          change (evaluated values i result).map ReadResult.state = _
          rw [loadEq]
          rfl
        · intro ref known
          by_cases same : ref.id = result.id
          · have equal : ref = result := by cases ref; cases result; cases same; rfl
            rw [equal, loadEq]
            simp [Schedule.run, Environment.set]
          · have earlier : prior.hasLoad ref.id = true := by
              simpa [Schedule.hasLoad, same] using known
            simpa [Schedule.run, Environment.set, same] using loadsEq ref earlier
      · cases found
    · cases found

private theorem selectValues_eq {input : Inputs params} {values : g.Valuation interpretation}
    (solves : g.Solves interpretation input values) (i : PEG.Index 0)
    (schedule : Schedule params nodes)
    (loaded : ∀ (r : PEG.Ref g.sort readTy), schedule.hasLoad r.id = true →
      (evaluated values i r).map ReadResult.value = (schedule.run input).loads r.id)
    (k : Nat) (roots : Tuple (PEG.Ref g.sort) (ReadTypes k))
    (registers : Tuple (fun _ => Fin nodes) (ReadTypes k))
    (found : selectValues g schedule k roots = some registers) :
    roots.map (fun _ => evaluated values i) = observeLoads (schedule.run input) k registers := by
  induction k with
  | zero =>
    cases roots
    cases found
    rfl
  | succ k ih =>
    cases roots with
    | cons first rest =>
      simp only [selectValues] at found
      split at found
      · rename_i result rootRow
        split at found
        · rename_i known
          simp only [Option.map_eq_some_iff] at found
          obtain ⟨otherRegisters, tail, rfl⟩ := found
          simp only [Tuple.map, observeLoads]
          rw [row_eq solves i first rootRow, ih rest otherRegisters tail]
          exact congrArg (fun value =>
            Tuple.cons (F := fun t => Option (interpretation.Value t)) (t := readValueTy) value
              (observeLoads (schedule.run input) k otherRegisters)) (loaded result known)
        · cases found
      · cases found

private theorem accepted_parts {phase : Fin nodes → Nat} {program : Program params reads nodes}
    (accepted : linearize g phase = .ok program)
    {token : PEG.Ref g.sort stateTy} {roots : Tuple (PEG.Ref g.sort) (ReadTypes reads)}
    (ordered : g.roots = .cons token roots) :
    PEG.DemandRank.check [.phase phase] g = true ∧
      trace g nodes token = some program.schedule ∧
      covers g program.schedule = true ∧
      selectValues g program.schedule reads roots = some program.valueRoots := by
  cases rank : PEG.DemandRank.check [.phase phase] g with
  | false => simp [linearize, rank] at accepted
  | true =>
    cases traced : trace g nodes token with
    | none => simp [linearize, rank, ordered, traced] at accepted
    | some schedule =>
      cases covered : covers g schedule with
      | false => simp [linearize, rank, ordered, traced, covered] at accepted
      | true =>
        cases selected : selectValues g schedule reads roots with
        | none => simp [linearize, rank, ordered, traced, covered, selected] at accepted
        | some registers =>
          have same : program = ⟨schedule, registers⟩ := by
            simpa [linearize, rank, ordered, traced, covered, selected] using accepted.symm
          subst program
          exact ⟨rfl, rfl, covered, selected⟩

theorem demandWellFounded {phase : Fin nodes → Nat} {program : Program params reads nodes}
    (accepted : linearize g phase = .ok program) : WellFounded g.Demand := by
  generalize ordered : g.roots = roots
  obtain ⟨_, _⟩ := roots
  exact g.demandWellFounded_of_check _ (accepted_parts accepted ordered).1

theorem effect_covered {phase : Fin nodes → Nat} {program : Program params reads nodes}
    (accepted : linearize g phase = .ok program) (id : Fin nodes)
    (effectful : isEffect (g.node id) = true) : id ∈ program.schedule.effects := by
  generalize ordered : g.roots = roots
  obtain ⟨_, _⟩ := roots
  have covered := (accepted_parts accepted ordered).2.2.1
  have cell := List.all_eq_true.mp covered id (by simp)
  simpa [effectful] using cell

theorem run_eq_observe {phase : Fin nodes → Nat} {program : Program params reads nodes}
    (accepted : linearize g phase = .ok program) (input : Inputs params) (i : PEG.Index 0)
    (wf : WellFounded g.Demand) :
    program.run input = g.observe interpretation (g.denote interpretation input wf) i := by
  generalize ordered : g.roots = roots
  cases roots with
  | cons token roots =>
    obtain ⟨_, traced, _, selected⟩ := accepted_parts accepted ordered
    have solves := g.denote_solves interpretation input wf
    obtain ⟨stateEq, loadEq⟩ := trace_eq solves i nodes token program.schedule traced
    have valuesEq := selectValues_eq solves i program.schedule loadEq reads roots program.valueRoots selected
    unfold PEG.Graph.observe
    rw [ordered]
    exact congrArg₂ Tuple.cons stateEq.symm valuesEq.symm

end Silmaril.SSA.Peggy.FieldHeap.Linearize.Proofs
