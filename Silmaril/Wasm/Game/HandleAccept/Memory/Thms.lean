module

public import Silmaril.Wasm.Game.HandleAccept.Memory.Defs
public import Silmaril.Wasm.Game.HandleAccept.Writer.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.Basic

/-!
# Memory-carrying writer imports: laws

* `inp_of_tsession`: every input tag of a traced session is decoded from a callout of an
  import **of the module** (`calloutAt?`), at its call (`callIn`) or at an answer to it
  (`answerIn`);
* `memWriterLang_subset_atoms`: a module none of whose imports is the `sexp` import accepts only
  atoms through memory-carrying writer imports, for every profile, environment class, memory
  index and policy without UB (no obligation).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.Memory

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.Handle Silmaril.Accept.IO Silmaril.Formats
  Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept.Writers

theorem inp_of_tsession {X I O C : Type} {P : Profile} {L : SEnv UImp} {m : Module}
    {memAddr : Option Nat} {R : Roles X I O C} {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    {p : IOAccept.Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) (i : I) (hi : Tag.inp i ∈ ts) :
    ∃ o, (∃ c, calloutAt? m memAddr c = some o) ∧
      (R.callIn o = some i ∨ ∃ wr, R.answerIn o wr = some i) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.tsession_inputs h i hi

/-- **Without a `sexp` import a module accepts only atoms.** -/
theorem memWriterLang_subset_atoms {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : MemImports} {pol : Policy (BitVec 32)}
    (hs : ∀ i ∈ m.imports, (i.moduleName, i.name) ≠ ix.sexp) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P Envs memIdx m ix pol ⊆ {x | ∃ a, x = .atom a} := by
  refine writerLang_subset_of_closed ha hw ?_
  rintro _ ⟨ts, ⟨_, _, _, -, _, _, -, _, _, _, hts⟩, rfl⟩ op args r hm
  have hi := (Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.mem_inputsOf hm).resolve_right
    (by simp)
  obtain ⟨o, ⟨c, hc⟩, hd | ⟨wr, hd⟩⟩ := inp_of_tsession hts _ hi
  · exact absurd hd Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.memAccept_not_write
  · rcases Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.memWrite_cases hd with
      he | ⟨a, rfl, rfl⟩
    · obtain ⟨i, hi, hio⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.Memory.calloutAt?_imp hc
      exact absurd (hio ▸ he) (hs i hi)
    · intro cs y _ hb _
      cases cs with
      | nil => cases hb; exact ⟨a, rfl⟩
      | cons _ _ => cases hb

end Silmaril.Wasm.Game.HandleAccept.Memory
