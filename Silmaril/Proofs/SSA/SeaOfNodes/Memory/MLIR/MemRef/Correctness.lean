module

public import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Thms
import Silmaril.SSA.MLIR.MemRef.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Proofs

open RVSDG (Locals Origin Port Tuple Wires)
open RVSDG.OrderedRuntime.Structured (Values newestIndex newestPort readOrigin read_cons)
open RVSDG.NestedTheta.ExplicitRuntime.Splice (olderIndex olderPort weaken)
open Silmaril.MLIR.MemRef (Buffer Ty Value model wordPorts run_yield run_prim load_effect store_effect)

variable {cells version : Nat} {args : List ValueSort} {past : List (List ValueSort)}
variable {scope : List (List (Ty cells))}

private abbrev BlockValues (cells : Nat) := Values (Value cells)

private theorem get_older {head : List (Ty cells)} {t : Ty cells} (x : Tuple (BlockValues cells) head) :
    (scope : List (List (Ty cells))) → (i : Fin scope.length) → (p : Port scope[i] t) →
    (env : Locals (BlockValues cells) scope) →
    ((env.snoc x).get (olderIndex head scope i)).get (olderPort head scope i p) = (env.get i).get p
  | [], i => i.elim0
  | front :: tail, i =>
    Fin.cases (motive := fun j => ∀ (p : Port (front :: tail)[j] t)
      (env : Locals (BlockValues cells) (front :: tail)),
      ((env.snoc x).get (olderIndex head (front :: tail) j)).get (olderPort head (front :: tail) j p) =
        (env.get j).get p)
      (fun _ _ => rfl) (fun j p env => get_older x tail j p env.2) i

private theorem read_weaken {head : List (Ty cells)} {t : Ty cells} (wire : Origin [] scope t)
    (env : Locals (BlockValues cells) scope) (x : Tuple (BlockValues cells) head) :
    readOrigin (weaken head wire) .nil (env.snoc x) = readOrigin wire .nil env := by
  cases wire with
  | arg p => cases p
  | output i p => exact get_older x scope i p env

private theorem get_newest {head : List (Ty cells)} {t : Ty cells} (port : Port head t)
    (env : Locals (BlockValues cells) scope) (x : Tuple (BlockValues cells) head) :
    ((env.snoc x).get (newestIndex head scope)).get (newestPort port scope) = x.get port := by
  induction scope with
  | nil => rfl
  | cons _ _ ih => exact ih env.2

private abbrev Reads (route : Routing cells args past scope) (input : Tuple (Val cells) args)
    (locals : Locals (Val cells) past) (env : Locals (BlockValues cells) scope) :=
  ∀ {s} (wire : Origin args past s), readOrigin (route wire) .nil env = encodeValue cells (readValue wire input locals)

private theorem after_load {route : Routing cells args past scope} {input : Tuple (Val cells) args}
    {locals : Locals (Val cells) past} {env : Locals (BlockValues cells) scope}
    (agree : Reads route input locals env) (word : Word) :
    Reads route.afterLoad input (.cons word .nil, locals)
      (env.snoc (.cons word .nil : Tuple (BlockValues cells) (wordPorts cells))) := by
  intro s wire
  cases wire with
  | arg port => exact (read_weaken (route (.arg port)) env _).trans (agree (.arg port))
  | output i port =>
    refine Fin.cases (motive := fun j => ∀ p : Port ([.word] :: past)[j] s,
      readOrigin (route.afterLoad (.output j p)) .nil
        (env.snoc (.cons word .nil : Tuple (BlockValues cells) (wordPorts cells))) =
          encodeValue cells (readValue (Origin.output (past := [.word] :: past) j p) input
            (.cons (t := ValueSort.word) word .nil, locals))) ?_ ?_ i port
    · intro p
      cases p with
      | head => exact get_newest .head env (.cons word .nil : Tuple (BlockValues cells) (wordPorts cells))
      | tail impossible => cases impossible
    · intro j p
      exact (read_weaken (route (.output j p)) env _).trans (agree (.output j p))

private theorem lowerBody_run (body : Body args past version)
    (route : Routing cells args past scope) (reference : Origin [] scope (.value .memref))
    (input : Tuple (Val cells) args) (locals : Locals (Val cells) past)
    (env : Locals (BlockValues cells) scope) (initial : Buffer cells)
    (agree : Reads route input locals env) :
    Silmaril.MLIR.MemRef.run (lowerBody body route reference) env initial =
      let result := body.denote input locals initial.cell
      ((.cons result.1 .nil : Tuple (BlockValues cells) (wordPorts cells)), ⟨result.2⟩) := by
  induction body generalizing scope initial with
  | ret _ word =>
    simp only [lowerBody, run_yield, Body.denote]
    erw [read_cons (route word) .nil .nil env]
    have same : readOrigin (route word) .nil env = readValue word input locals := agree word
    exact congrArg (fun w : Word => ((.cons w .nil : Tuple (BlockValues cells) (wordPorts cells)), initial))
      same
  | load _ address rest ih =>
    simp only [lowerBody, run_prim, Body.denote]
    have loaded : (model cells).effect .load
        (Wires.read (.cons reference (.cons (route address) .nil)) .nil env) initial =
        (.cons (initial.cell (readOrigin (route address) .nil env)) .nil, initial) := by
      erw [read_cons reference (.cons (route address) .nil) .nil env, read_cons (route address) .nil .nil env]
      exact load_effect (readOrigin reference .nil env) (readOrigin (route address) .nil env) initial
    rw [loaded, agree address]
    exact ih route.afterLoad (weaken (wordPorts cells) reference)
      (.cons (initial.cell (readValue address input locals)) .nil, locals) _ initial
      (after_load agree (initial.cell (readValue address input locals)))
  | store _ address word rest ih =>
    simp only [lowerBody, run_prim, Body.denote]
    have stored : (model cells).effect .store
        (Wires.read (.cons (route word) (.cons reference (.cons (route address) .nil))) .nil env) initial =
        (.nil, ⟨Function.update initial.cell (readOrigin (route address) .nil env)
          (readOrigin (route word) .nil env)⟩) := by
      erw [read_cons (route word) (.cons reference (.cons (route address) .nil)) .nil env,
        read_cons reference (.cons (route address) .nil) .nil env, read_cons (route address) .nil .nil env]
      exact store_effect (readOrigin (route word) .nil env) (readOrigin reference .nil env)
        (readOrigin (route address) .nil env) initial
    rw [stored, agree address, agree word]
    exact ih (fun wire => weaken [] (route wire)) (weaken [] reference) locals _ _
      (fun wire => (read_weaken (route wire) env .nil).trans (agree wire))

private theorem encode_get {s : ValueSort} (port : Port args s) (input : Tuple (Val cells) args) :
    (encodeScalars cells input).get (scalarPort port) = encodeValue cells (input.get port) := by
  induction port with
  | head => cases input; rfl
  | tail _ ih => cases input with | cons _ tail => exact ih tail

private theorem entry_reads (input : Tuple (Val cells) args) :
    Reads (Routing.entry cells args) input PUnit.unit (encodeInput input, PUnit.unit) := by
  intro s wire
  cases wire with
  | arg port => exact encode_get port input
  | output i _ => exact i.elim0

theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (initial : Buffer cells) :
    observe graph input initial =
      let result := graph.denote input initial.cell
      (result.1, ⟨result.2⟩) := by
  unfold observe lower
  erw [lowerBody_run graph (Routing.entry cells args) (.output 0 .head) input PUnit.unit
    (encodeInput input, PUnit.unit) initial (entry_reads input)]
  rfl

theorem lower_returns_iff (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells)
    (word : Word) (final : Heap cells) :
    graph.Returns input initial word final ↔ observe graph input ⟨initial⟩ = (word, ⟨final⟩) := by
  rw [graph.returns_iff_denote, lower_run]
  constructor
  · intro equal
    exact congrArg (fun result : Word × Heap cells => (result.1, Buffer.mk result.2)) equal
  · intro equal
    exact congrArg (fun result : Word × Buffer cells => (result.1, result.2.cell)) equal

end Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Proofs
