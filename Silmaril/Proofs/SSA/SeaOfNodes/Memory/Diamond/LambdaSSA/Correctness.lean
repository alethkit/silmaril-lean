module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
import Silmaril.SSA.PhiView.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA

open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes
open SeaOfNodes.Diamond (Projection Slot)
open Memory (Address Heap Val ValueSort Word readValue)
open Memory.Diamond.LambdaSSA
open RVSDG (Locals Origin Port Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {args : List ValueSort} {past : List (List ValueSort)} {context labels : List Code}
variable {cells version : Nat}

private theorem instruction_deterministic : Semantics.InstrDeterministic (Instruction cells) := by
  intro op arg initial a heapA b heapB first second
  cases first <;> cases second <;> exact ⟨rfl, rfl⟩

private theorem argument_match (input : Tuple (Val cells) args) {sort : ValueSort}
    (p : Port args sort) :
    inputEnv input (argumentRef p).val = encode (input.get p) := by
  induction p with
  | head => cases input; rfl
  | tail p ih => cases input with | cons _ rest => exact ih rest

private theorem entry_match (input : Tuple (Val cells) args) :
    Matches (Routing.entry args) (inputEnv input) input PUnit.unit := by
  intro sort wire
  cases wire with
  | arg p => exact argument_match input p
  | output i _ => exact i.elim0

private theorem weaken_match {route : Routing args past context} {env : Env (Atom cells)}
    {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (A : Code) (value : Value (Atom cells)) :
    Matches (Routing.weaken A route) (extend env value) input locals :=
  fun wire => matched wire

private theorem afterLoad_match {route : Routing args past context} {env : Env (Atom cells)}
    {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (word : Word) :
    Matches (Routing.afterLoad route) (extend env (encode (sort := .word) word))
      input (.cons word .nil, locals) := by
  intro sort wire
  cases wire with
  | arg p => exact matched (.arg p)
  | output i p =>
    refine Fin.cases (motive := fun j => ∀ port : Port ([.word] :: past)[j] sort,
      (extend env (encode (sort := .word) word) ((Routing.afterLoad route (.output j port)).val)) =
        encode (readValue (Origin.output (past := [.word] :: past) j port) input
          (Tuple.cons (F := Val cells) (t := ValueSort.word) word .nil, locals))) ?_ ?_ i p
    · intro port
      cases port with
      | head => rfl
      | tail impossible => cases impossible
    · intro j port
      exact matched (.output j port)

private theorem schedule_typed (body : Memory.Body args past version)
    (route : Routing args past context) {tail : Region Opcode}
    (typed : tail.HasType (schedule body route).context labels) :
    (prepend (schedule body route).statements tail).HasType context labels := by
  induction body generalizing context with
  | ret => exact typed
  | load memory address rest ih =>
    exact .let₁ (.op (.var (route address).property)) (ih (Routing.afterLoad route) typed)
  | store memory address source rest ih =>
    exact .let₁ (.op (.pair (.var (route address).property) (.var (route source).property)))
      (ih (Routing.weaken .unit route) typed)

theorem body_hasType (body : Memory.Body args past version) (route : Routing args past context)
    {label : Nat} (target : At labels label wordPacket) :
    ((schedule body route).emit label).HasType context labels :=
  schedule_typed body route (.br target (PhiView.packTerm_hasType (schedule body route).arguments))

private theorem schedule_eval (body : Memory.Body args past version)
    {route : Routing args past context} {env : Env (Atom cells)}
    {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (initial : Heap cells) {tail : Region Opcode}
    {label : Nat} {payload : Value (Atom cells)} {final : Heap cells}
    (runTail : ∀ finalEnv,
      finalEnv (schedule body route).result.val = encode (sort := .word) (body.denote input locals initial).1 →
      Semantics.Region.Eval (Instruction cells) finalEnv tail (body.denote input locals initial).2
        label payload final) :
    Semantics.Region.Eval (Instruction cells) env (prepend (schedule body route).statements tail)
      initial label payload final := by
  induction body generalizing context env initial with
  | ret memory source => exact runTail env (matched source)
  | load memory address rest ih =>
    refine .let₁ (.op (Semantics.Tm.Eval.var_of_eq (matched address)) (.load _ _)) ?_
    exact ih (afterLoad_match matched _) initial runTail
  | store memory address source rest ih =>
    refine .let₁ (.op (.pair (Semantics.Tm.Eval.var_of_eq (matched address))
      (Semantics.Tm.Eval.var_of_eq (matched source))) (.store _ _ _)) ?_
    exact ih (weaken_match matched .unit .unit) _ runTail

theorem body_eval (body : Memory.Body args past version) {route : Routing args past context}
    {env : Env (Atom cells)} {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
    (matched : Matches route env input locals) (initial : Heap cells) (label : Nat) :
    Semantics.Region.Eval (Instruction cells) env ((schedule body route).emit label) initial label
      (packet (body.denote input locals initial).1) (body.denote input locals initial).2 :=
  schedule_eval body matched initial (fun _ equal => .br (.pair (Semantics.Tm.Eval.var_of_eq equal) .unit))

variable (g : Memory.Diamond.Graph args)

private abbrev cfgLabels : List Code := [.unit, .unit, wordPacket, wordPacket]

theorem lower_hasType : (lower g).HasType (entryContext args) [wordPacket] := by
  refine .cfg blockTypes (.case (A := .unit) (B := .unit) (.var (i := 0) rfl)
    (.br (ℓ := 0) rfl .unit) (.br (ℓ := 1) rfl .unit)) ?_
  have armTyped (p : Projection) :
      ((armSchedule g p).emit 2).HasType (.unit :: entryContext args) cfgLabels :=
    body_hasType (g.arm p) (armRouting args) (label := 2) rfl
  refine Fin.cases (armTyped .onTrue) (Fin.cases (armTyped .onFalse) ?_)
  intro _
  exact .let₂ (A := wordCode) (B := .unit) (.var (i := 0) rfl)
    (body_hasType g.suffix (suffixRouting args) (label := 3) rfl)

private theorem arm_match (guard : Bool) (input : Tuple (Val cells) args) :
    Matches (armRouting args) (extend (entryEnv guard input) .unit) input PUnit.unit :=
  weaken_match (weaken_match (entry_match input) guardCode (guardValue guard)) .unit .unit

private theorem suffix_match (guard : Bool) (input : Tuple (Val cells) args) (word : Word) :
    Matches (suffixRouting args)
      (extend (extend (extend (entryEnv guard input) (packet word)) (encode (sort := .word) word)) .unit)
      (.cons word input) PUnit.unit := by
  intro sort wire
  cases wire with
  | arg p =>
    cases p with
    | head => rfl
    | tail p => exact argument_match input p
  | output i _ => exact i.elim0

theorem arm_eval (p : Projection) (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    Semantics.Region.Eval (Instruction cells) (extend (entryEnv guard input) .unit) ((armSchedule g p).emit 2)
      initial 2 (packet ((g.arm p).denote input initial).1) ((g.arm p).denote input initial).2 := by
  refine schedule_eval (g.arm p) (arm_match guard input) initial ?_
  intro env value
  apply (PhiView.latch_eq_transfer (Instruction cells) (phiView g) (incoming g p) _ _ _ _ _).mpr
  refine ⟨rfl, ?_, rfl⟩
  exact congrArg (fun word => Value.pair word .unit) value.symm

private theorem suffix_eval (guard : Bool) (input : Tuple (Val cells) args) (selected : Word × Heap cells) :
    Semantics.Region.Eval (Instruction cells) (extend (entryEnv guard input) (packet selected.1)) (suffix g)
      selected.2 3 (packet (g.suffix.denote (.cons selected.1 input) selected.2).1)
      (g.suffix.denote (.cons selected.1 input) selected.2).2 :=
  .let₂ .var (body_eval g.suffix (suffix_match guard input selected.1) selected.2 3)

private theorem lower_eval_denote (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells) :
    Semantics.Region.Eval (Instruction cells) (entryEnv guard input) (lower g) initial 0
      (packet (g.denote guard input initial).1) (g.denote guard input initial).2 := by
  have join (selected : Word × Heap cells) :
      Semantics.Region.Follow (Instruction cells) (entryEnv guard input) (blocks g) 2
        (packet selected.1) selected.2 0 (packet (g.suffix.denote (.cons selected.1 input) selected.2).1)
        (g.suffix.denote (.cons selected.1 input) selected.2).2 :=
    .step (next := 3) (by decide) (suffix_eval g guard input selected) (.exit (Nat.le_refl 3))
  cases guard with
  | false =>
    refine .cfg (.case_inr Semantics.Tm.Eval.var (.br .unit)) ?_
    refine .step (next := 2) (by decide) ?_ (join ((g.arm .onFalse).denote input initial))
    exact arm_eval g .onFalse false input initial
  | true =>
    refine .cfg (.case_inl Semantics.Tm.Eval.var (.br .unit)) ?_
    refine .step (next := 2) (by decide) ?_ (join ((g.arm .onTrue).denote input initial))
    exact arm_eval g .onTrue true input initial

theorem lower_eval_iff (guard : Bool) (input : Tuple (Val cells) args) (initial final : Heap cells)
    (label : Nat) (payload : Value (Atom cells)) :
    Semantics.Region.Eval (Instruction cells) (entryEnv guard input) (lower g) initial label payload final ↔
      label = 0 ∧ payload = packet (g.denote guard input initial).1 ∧ final = (g.denote guard input initial).2 := by
  constructor
  · intro observed
    exact observed.deterministic instruction_deterministic (lower_eval_denote g guard input initial)
  · rintro ⟨rfl, rfl, rfl⟩
    exact lower_eval_denote g guard input initial

theorem returns_iff (guard : Bool) (input : Tuple (Val cells) args) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    g.Returns guard input initial word final ↔
      Semantics.Region.Eval (Instruction cells) (entryEnv guard input) (lower g) initial 0 (packet word) final := by
  rw [g.returns_iff_denote, lower_eval_iff]
  constructor
  · intro same
    rw [same]
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨_, value, heap⟩
    have equal : word = (g.denote guard input initial).1 :=
      Sum.inr.inj (Value.atom.inj (Value.pair.inj value).1)
    exact Prod.ext equal.symm heap.symm

end Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.LambdaSSA
