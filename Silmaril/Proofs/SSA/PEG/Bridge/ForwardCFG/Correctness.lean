module

public import Silmaril.SSA.PEG.Bridge.ForwardCFG.Defs
public import Silmaril.SSA.PEG.Bridge.MLIR.Thms
public import Silmaril.SSA.LambdaRTL.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Thms
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.ForwardCFG.Proofs

open RVSDG (Port Tuple Origin Wires Locals)
open Silmaril.SSA.LambdaRTL (Region CFG Val obs upd)
open Silmaril.SSA.PEG.Bridge.ForwardCFG.Compiler

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results ts : List (Ty Data)} {n : Nat}
variable {past sigs : List (List (ValuePort Data))}

theorem unpack_pack [DecidableEq Data] {C : Ty Data → Type} (xs : Tuple C ts) :
    (Value.pack xs).unpack ts = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Value.pack, Value.unpack, ih]

variable (m : TotalModel P)

private theorem argValue_get (env : Tuple m.toPEG.Value params)
    {t : ValuePort Data} (p : Port (valuePorts params) t) :
    argValue env (portIndex p) = encodePort m t ((toPorts (F := m.toRVSDG.Val) env).get p) := by
  induction params with
  | nil => cases p
  | cons t ts ih =>
    cases env with
    | cons x xs =>
      cases p with
      | head => rfl
      | tail p => exact ih xs p

theorem inputStore_inputs (env : Tuple m.toPEG.Value params) :
    Inputs m env (inputStore m env) :=
  fun p => argValue_get m env p

private abbrev LocalsMatch (locals : Locals m.toRVSDG.Val past) (store : Store m) : Prop :=
  ∀ (j : Fin past.length) {t : ValuePort Data} (p : Port past[j] t),
    store (.temp j.val) = encodePort m t ((locals.get j).get p)

private theorem readOlder {F : ValuePort Data → Type}
    (past : List (List (ValuePort Data))) {head : List (ValuePort Data)}
    (locals : Locals F past) (output : Tuple F head) (j : Fin (past ++ [head]).length)
    (earlier : j.val < past.length) {t : ValuePort Data} (p : Port (past ++ [head])[j] t) :
    ((locals.snoc output).get j).get p =
      (locals.get ⟨j.val, earlier⟩).get (List.getElem_append_left earlier ▸ p) := by
  induction past with
  | nil => exact (Nat.not_lt_zero _ earlier).elim
  | cons a past ih =>
    revert earlier p
    refine Fin.cases ?_ ?_ j
    · intros
      rfl
    · intro i earlier p
      exact ih locals.2 i (Nat.lt_of_succ_lt_succ earlier) p

private theorem readLast {F : ValuePort Data → Type} (past : List (List (ValuePort Data)))
    {head : List (ValuePort Data)} (locals : Locals F past) (output : Tuple F head)
    {t : ValuePort Data} (p : Port (past ++ [head])[past.length] t) :
    ((locals.snoc output).get ⟨past.length, by simp⟩).get p =
      output.get ((by simp : (past ++ [head])[past.length] = head) ▸ p) := by
  induction past with
  | nil => rfl
  | cons a past ih => exact ih locals.2 p

private theorem localsMatch_snoc (locals : Locals m.toRVSDG.Val past) (store : Store m)
    (agree : LocalsMatch m locals store) {out : Ty Data} (x : m.toPEG.Value out) :
    LocalsMatch m (locals.snoc (head := valuePorts [out]) (.cons x .nil))
      (upd store (.temp past.length) (.atom out x)) := by
  intro j t p
  by_cases old : j.val < past.length
  · have neq : Register.temp j.val ≠ .temp past.length :=
      fun eq => (Nat.ne_of_lt old) (Register.temp.inj eq)
    have reads := readOlder past locals
      (.cons x .nil : Tuple m.toRVSDG.Val (valuePorts [out])) j old p
    simp only [upd, ite_eq_right neq]
    exact (agree ⟨j.val, old⟩ (List.getElem_append_left old ▸ p)).trans
      (congrArg (encodePort m t) reads.symm)
  · have atEnd : j.val = past.length := by
      have h := j.isLt
      simp at h
      omega
    have indexEq : j = ⟨past.length, by simp⟩ := Fin.ext atEnd
    subst j
    have reads := readLast past locals
      (.cons x .nil : Tuple m.toRVSDG.Val (valuePorts [out])) p
    simp only [upd, ↓reduceIte]
    rw [reads]
    generalize ((by simp : (past ++ [valuePorts [out]])[past.length] = valuePorts [out]) ▸ p) = q
    cases q with
    | head => rfl
    | tail q => cases q

private theorem inputs_upd (env : Tuple m.toPEG.Value params) (store : Store m)
    (agree : Inputs m env store) (i : Nat) (x : Value m.toPEG.Value) :
    Inputs m env (upd store (.temp i) x) := by
  intro t p
  exact (ite_eq_right (by intro h; cases h)).trans (agree p)

private def packPorts :
    {ports : List (ValuePort Data)} → Tuple m.toRVSDG.Val ports → Value m.toPEG.Value
  | _, .nil => .unit
  | _, .cons x xs => .pair (encodePort m _ x) (packPorts xs)

private theorem packPorts_value (xs : Tuple m.toRVSDG.Val (valuePorts ts)) :
    packPorts m xs = Value.pack (fromPorts ts xs) := by
  induction ts with
  | nil => cases xs; rfl
  | cons t ts ih =>
    cases xs with
    | cons x xs => exact congrArg (Value.pair (Value.atom t x)) (ih xs)

variable [DecidableEq Data]

private theorem wireTuple_eval {ports : List (ValuePort Data)}
    (env : Tuple m.toPEG.Value params) (locals : Locals m.toRVSDG.Val past) (store : Store m)
    (input : Inputs m env store) (agree : LocalsMatch m locals store)
    (wires : Wires (valuePorts params) past ports) :
    (wireTuple wires).eval (model m) store =
      packPorts m (wires.read (toPorts (F := m.toRVSDG.Val) env) locals) := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p => exact congrArg₂ Value.pair (input p) ih
    | output j p => exact congrArg₂ Value.pair (agree j p) ih

private theorem evalSSA_lowerTerm :
    {past sigs : List (List (ValuePort Data))} →
    (term : RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)) →
    (live : Prefix past) → (env : Tuple m.toPEG.Value params) → (locals : Locals m.toRVSDG.Val past) →
    (store : Store m) → Inputs m env store → LocalsMatch m locals store →
    (lowerTerm term live).evalSSA (model m) store =
      some ((), Value.pack (fromPorts results
        (term.eval m.toRVSDG (toPorts (F := m.toRVSDG.Val) env) locals)))
  | _, _, .ret wires, _, env, locals, store, input, agree => by
    have h := (wireTuple_eval m env locals store input agree wires).trans
      (packPorts_value m (wires.read (toPorts (F := m.toRVSDG.Val) env) locals))
    exact congrArg (fun payload => some ((), payload)) h
  | past, _, .bind node _ rest, live, env, locals, store, input, agree => by
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | gamma _ =>
      cases wires with
      | cons selector _ => exact (live.noControl selector).elim
    | simple opcode =>
      cases opcode with
      | @apply ins out op =>
        let args := fromPorts ins (wires.read (toPorts (F := m.toRVSDG.Val) env) locals)
        let value := op.eval m args
        have read : (wireTuple wires).eval (model m) store = Value.pack args :=
          (wireTuple_eval m env locals store input agree wires).trans (packPorts_value m _)
        have app : (model m).app ⟨ins, out, op⟩ ((wireTuple wires).eval (model m) store) =
            some (Value.atom out value) := by
          rw [read]
          change ((Value.pack args).unpack ins).map (fun xs => Value.atom out (op.eval m xs)) = _
          rw [unpack_pack]
          rfl
        change ((model m).app ⟨ins, out, op⟩ ((wireTuple wires).eval (model m) store) >>=
          fun v => (lowerTerm rest (live.snoc out)).evalSSA (model m)
            (upd store (.temp past.length) v)) =
          some ((), Value.pack (fromPorts results
            (rest.eval m.toRVSDG (toPorts (F := m.toRVSDG.Val) env)
              (locals.snoc (head := valuePorts [out]) (.cons value .nil)))))
        rw [app]
        exact evalSSA_lowerTerm rest (live.snoc out) env _ _
          (inputs_upd m env store input _ _) (localsMatch_snoc m locals store agree value)
termination_by _ sigs => sigs.length
decreasing_by simp_wf

theorem evalSSA_fromRVSDG
    (g : RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results))
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    (fromRVSDG g).evalSSA (model m) store =
      some ((), Value.pack (fromPorts results
        (g.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env)))) := by
  rw [← RVSDG.Graph.run_toTerm]
  exact evalSSA_lowerTerm m g.toTerm Prefix.empty env PUnit.unit store input (fun j => j.elim0)

omit [DecidableEq Data] in
private theorem lowerTerm_layout :
    {past sigs : List (List (ValuePort Data))} →
    (term : RVSDG.Term (Opcode P) (valuePorts params) past sigs (valuePorts results)) →
    (live : Prefix past) →
    let r := lowerTerm term live
    r.NoClobber ∧ (∀ labels path, r.blocks labels path = []) ∧
      ∀ reg ∈ r.bound, ∃ i, reg = .temp i ∧ past.length ≤ i ∧ i < past.length + sigs.length
  | _, _, .ret _, _ => by
    change True ∧ (∀ _ _, [] = ([] : List ((Unit ⊕ CFG.Path) × CFG.Block Register _ (Instruction P)))) ∧
      ∀ reg ∈ (∅ : Finset Register), _
    exact ⟨trivial, fun _ _ => rfl, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | past, _, .bind node _ rest, live => by
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | gamma _ =>
      cases wires with
      | cons selector _ => exact (live.noControl selector).elim
    | simple opcode =>
      cases opcode with
      | @apply ins out op =>
        obtain ⟨safe, blocks, bound⟩ := lowerTerm_layout rest (live.snoc out)
        refine ⟨safe, blocks, ?_⟩
        intro reg h
        change reg ∈ insert (.temp past.length) (lowerTerm rest (live.snoc out)).bound at h
        rcases Finset.mem_insert.mp h with rfl | old
        · exact ⟨past.length, rfl, Nat.le_refl _, by simp⟩
        · obtain ⟨i, rfl, lo, hi⟩ := bound reg old
          simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at lo hi
          exact ⟨i, rfl, by omega, by simp; omega⟩
termination_by _ sigs => sigs.length
decreasing_by simp_wf

omit [DecidableEq Data] in
theorem cfg_blocks (g : Graph P params results n 0) (ordered : Ordered g) :
    (toCFG g ordered).blocks = [] :=
  (lowerTerm_layout (translate g ordered).2.toTerm Prefix.empty).2.1 _ _

theorem evalRTL_fromRVSDG
    (g : RVSDG.Graph (Opcode P) (valuePorts params) [] sigs (valuePorts results))
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    ∃ final : Store m,
      (fromRVSDG g).evalRTL (model m) store = some ((), Value.pack (fromPorts results
        (g.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))), final) ∧
      ∀ reg, ReadOnly sigs.length reg → final reg = store reg := by
  let r := fromRVSDG g
  obtain ⟨safe, _, written⟩ := lowerTerm_layout g.toTerm Prefix.empty
  have observed := (Region.evalObs_eq_evalSSA (model m) (r := r) safe store).trans
    (evalSSA_fromRVSDG m g env store input)
  cases run : r.evalRTL (model m) store with
  | none =>
    simp [Region.evalObs, run] at observed
  | some output =>
    obtain ⟨exit, payload, final⟩ := output
    have result := Option.some.inj (by
      simpa [Region.evalObs, run, obs] using observed :
      some (exit, payload) = some ((), Value.pack (fromPorts results
        (g.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env)))))
    cases result
    refine ⟨final, rfl, ?_⟩
    intro reg readOnly
    have outside : reg ∉ r.bound := by
      intro h
      obtain ⟨i, rfl, _, hi⟩ := written reg h
      exact (Nat.not_lt_of_ge readOnly) (by simpa only [List.length_nil, Nat.zero_add] using hi)
    have frame := Region.evalRTL_frame (model m) r store
      (fun e => some (e.2.2 reg)) (fun _ => some (store reg))
      (fun _ _ _ agrees => congrArg some (agrees reg outside))
    rw [run] at frame
    exact Option.some.inj frame

theorem cfg_run (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    ∃ final : Store m,
      (toCFG g ordered).run (model m) store = some (Sum.inl (), Value.pack (fromPorts results
        ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))), final) ∧
      ∀ reg, ReadOnly (translate g ordered).1.length reg → final reg = store reg := by
  obtain ⟨final, run, frame⟩ := evalRTL_fromRVSDG m (translate g ordered).2 env store input
  refine ⟨final, ?_, frame⟩
  rw [toCFG, CFG.run_flatten, toLambdaRTL, run]
  rfl

theorem observeCFG_rvsdg (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    observeCFG g ordered m store = some (Sum.inl (), fromPorts results
      ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))) := by
  obtain ⟨_, run, _⟩ := cfg_run m g ordered env store input
  rw [observeCFG, run]
  let out : Tuple m.toPEG.Value results :=
    fromPorts results ((translate g ordered).2.run m.toRVSDG (toPorts (F := m.toRVSDG.Val) env))
  exact congrArg (Option.map (fun xs => (Sum.inl (), xs))) (unpack_pack out)

theorem observeCFG_peg (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store)
    (idx : Index 0) (wf : WellFounded g.Demand) :
    (observeCFG g ordered m store).map (fun e => (e.1, e.2.map (fun _ => some))) =
      some (Sum.inl (), g.observe m.toPEG (g.denote m.toPEG env wf) idx) := by
  rw [observeCFG_rvsdg m g ordered env store input, observe_translate g ordered m env idx wf]
  rfl

open Silmaril.SSA.RVSDG.MLIR

omit [DecidableEq Data] in
private theorem someTuple_injective {C : Ty Data → Type} {a b : Tuple C ts}
    (eq : a.map (fun _ => some) = b.map (fun _ => some)) : a = b := by
  induction a with
  | nil => cases b; rfl
  | cons x xs ih =>
    cases b with
    | cons y ys =>
      have head : some x = some y := congrArg (fun xs => xs.get .head) eq
      have tail : xs.map (fun _ => some) = ys.map (fun _ => some) :=
        congrArg (fun | .cons _ tail => tail) eq
      exact congrArg₂ Tuple.cons (Option.some.inj head) (ih tail)

theorem observeCFG_mlir (g : Graph P params results n 0) (ordered : Ordered g)
    (env : Tuple m.toPEG.Value params) (store : Store m) (input : Inputs m env store) :
    observeCFG g ordered m store =
      some (Sum.inl (), fromPorts results (Regionless.ofAssignment (F := m.toRVSDG.Val) results (fun i =>
        (translateMLIR g ordered i).denote m.toMLIR
          (Regionless.toAssignment params (toPorts (F := m.toRVSDG.Val) env))))) := by
  rw [observeCFG_rvsdg m g ordered env store input]
  have rv := observe_translate g ordered m env Fin.elim0 ordered.demandWellFounded
  have mlir := observe_translateMLIR g ordered m env Fin.elim0 ordered.demandWellFounded
  exact congrArg (fun out => some (Sum.inl (), out)) (someTuple_injective (rv.symm.trans mlir))

end Silmaril.SSA.PEG.Bridge.ForwardCFG.Proofs
