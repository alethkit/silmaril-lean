module

public import Silmaril.SSA.SeaOfNodes.Memory.Defs

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Proofs

open RVSDG (Locals Tuple)

variable {args : List ValueSort} {past : List (List ValueSort)} {version cells : Nat}
variable {input : Tuple (Val cells) args} {locals : Locals (Val cells) past}
variable {states : Snapshots cells version} {body : Body args past version}
variable {value : Word} {final : Heap cells}

private theorem push_last (states : Snapshots cells version) (updated : Heap cells) :
    states.push updated (Fin.last (version + 1)) = updated :=
  Fin.lastCases_last

private theorem exec_denote (run : body.Exec input locals states value final) :
    body.denote input locals (states (Fin.last version)) = (value, final) := by
  induction run with
  | ret memory source locals states => simp only [Body.denote, MemoryInput.current]
  | load next ih => simpa only [Body.denote, MemoryInput.current] using ih
  | store next ih => simpa only [Body.denote, MemoryInput.current, push_last] using ih

private theorem denote_exec (eq : body.denote input locals (states (Fin.last version)) = (value, final)) :
    body.Exec input locals states value final := by
  induction body with
  | ret memory source =>
    simp only [Body.denote] at eq
    rcases Prod.mk.inj eq with ⟨rfl, rfl⟩
    simpa only [MemoryInput.current] using (Body.Exec.ret (input := input) memory source locals states)
  | load memory address rest ih =>
    apply Body.Exec.load
    apply ih
    simpa only [Body.denote, MemoryInput.current] using eq
  | store memory address source rest ih =>
    apply Body.Exec.store
    apply ih
    simpa only [Body.denote, MemoryInput.current, push_last] using eq

theorem exec_iff_denote :
    body.Exec input locals states value final ↔
      body.denote input locals (states (Fin.last version)) = (value, final) :=
  ⟨exec_denote, denote_exec⟩

end Silmaril.SSA.SeaOfNodes.Memory.Proofs
