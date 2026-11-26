module

public import Silmaril.SSA.SeaOfNodes.Loop.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # A scheduled counted-swap profile of a Sea of Nodes loop -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

open Diamond (Model Val ValueSort dataPorts)
open RVSDG (Port Tuple)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region Terminator Tm)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)

universe u v

abbrev word : ValueSort Unit := .data ()
abbrev wordPort : Diamond.Ty Unit := .value word
abbrev wordCode : Silmaril.Ty Unit := .base ()
abbrev predicateCode : Silmaril.Ty Unit := .coprod .unit .unit

inductive Op : Diamond.Signature Unit where
  | seed : Op [] word
  | test : Op [word, word] .predicate
  | advance : Op [word] word
  | observe : Op [word, word] word

/-- Inputs are the limit and an initial pair. The loop carries that pair
and an index; the backedge swaps the pair and advances the index. -/
def graph : Graph Op [word, word, word] [word, word, word]
    [[wordPort]] [[.value .predicate], [wordPort], [wordPort]] word where
  preheader := .cons .seed .nil .nil
  header :=
    let index : Port (headerPorts [word, word, word] [word, word, word]) wordPort :=
      .tail (.tail (.tail (.tail (.tail .head))))
    let first : Port (headerPorts [word, word, word] [word, word, word]) wordPort :=
      .tail (.tail (.tail .head))
    let second : Port (headerPorts [word, word, word] [word, word, word]) wordPort :=
      .tail (.tail (.tail (.tail .head)))
    .cons .test (.cons (.arg index) (.cons (.arg .head) .nil))
      (.cons .advance (.cons (.arg index) .nil)
        (.cons .observe (.cons (.arg first) (.cons (.arg second) .nil)) .nil))
  phiInputs
    | .entry => .cons (.arg (.tail .head)) (.cons (.arg (.tail (.tail .head)))
        (.cons (.output (0 : Fin 1) .head) .nil))
    | .backedge => .cons (.arg (.tail (.tail (.tail (.tail .head)))))
        (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.output (1 : Fin 3) .head) .nil))
  predicate := .output (0 : Fin 3) .head
  result := .output (2 : Fin 3) .head

variable (m : Model.{0,0,u} Op)

abbrev Word := m.value ()

structure Inputs (α : Type u) where
  limit : α
  first : α
  second : α

abbrev Carried := Tuple (Val m.value) (dataPorts [word, word, word])

def input (args : Inputs (Word m)) : Tuple (Val m.value) (dataPorts [word, word, word]) :=
  .cons args.limit (.cons args.first (.cons args.second .nil))

def carried (a b i : Word m) : Carried m :=
  .cons a (.cons b (.cons i .nil))

def seed : Word m := m.run .seed .nil
def test (i limit : Word m) : Bool := (m.run .test (.cons i (.cons limit .nil))).down
def advance (i : Word m) : Word m := m.run .advance (.cons i .nil)
def observe (a b : Word m) : Word m := m.run .observe (.cons a (.cons b .nil))

/-- Each target opcode interprets exactly one source primitive. -/
inductive Opcode where
  | seed
  | test
  | advance
  | observe

instance : HasTy Opcode (Silmaril.Ty Unit) where
  src
    | .seed => .unit
    | .test | .observe => PhiView.packedType [wordCode, wordCode]
    | .advance => PhiView.packedType [wordCode]
  trg
    | .test => predicateCode
    | .seed | .advance | .observe => wordCode

def selector (b : Bool) : Value (Word m) :=
  if b then .inl .unit else .inr .unit

def run : Opcode → Value (Word m) → Option (Value (Word m))
  | .seed, .unit => some (.atom (seed m))
  | .test, .pair (.atom i) (.pair (.atom limit) .unit) => some (selector m (test m i limit))
  | .advance, .pair (.atom i) .unit => some (.atom (advance m i))
  | .observe, .pair (.atom a) (.pair (.atom b) .unit) => some (.atom (observe m a b))
  | _, _ => none

def instruction {σ : Type v} (op : Opcode) (arg : Value (Word m)) (start : σ)
    (result : Value (Word m)) (finish : σ) : Prop :=
  run m op arg = some result ∧ finish = start

def inputEnv (args : Inputs (Word m)) : Env (Word m)
  | 0 => .atom args.limit
  | 1 => .atom args.first
  | 2 => .atom args.second
  | _ + 3 => .unit

def packCarried : Carried m → Value (Word m)
  | .cons a (.cons b (.cons i .nil)) => .pair (.atom a) (.pair (.atom b) (.pair (.atom i) .unit))

def packResult (result : Word m) : Value (Word m) := .pair (.atom result) .unit

def stepLabel : Word m ⊕ Carried m → Nat
  | .inl _ => 1
  | .inr _ => 0

def stepPayload : Word m ⊕ Carried m → Value (Word m)
  | .inl result => packResult m result
  | .inr next => packCarried m next

abbrev inputContext := [wordCode, wordCode, wordCode]
abbrev carriedType := PhiView.packedType [wordCode, wordCode, wordCode]
abbrev returnType := PhiView.packedType [wordCode]

/-- After three destructurings, the old index, second and first are at
indices one, three and five. The captured limit is at index seven. -/
abbrev unpackedContext : List (Silmaril.Ty Unit) :=
  [.unit, wordCode, returnType, wordCode, PhiView.packedType [wordCode, wordCode],
    wordCode, carriedType] ++ inputContext

abbrev afterHeader := wordCode :: wordCode :: predicateCode :: unpackedContext

def three {Γ : List (Silmaril.Ty Unit)} (a b i : PhiView.Operand Γ wordCode) :
    PhiView.Arguments Γ [wordCode, wordCode, wordCode] :=
  fun j => Fin.cases a (Fin.cases b (Fin.cases i (fun k => (Nat.not_lt_zero _ k.isLt).elim))) j

def entryArgs : PhiView.Arguments (wordCode :: inputContext) [wordCode, wordCode, wordCode] :=
  three ⟨2, rfl⟩ ⟨3, rfl⟩ ⟨0, rfl⟩

def backedgeArgs : PhiView.Arguments (.unit :: afterHeader) [wordCode, wordCode, wordCode] :=
  three ⟨7, rfl⟩ ⟨9, rfl⟩ ⟨2, rfl⟩

def exitArgs : PhiView.Arguments (.unit :: afterHeader) [wordCode] :=
  fun i => Fin.cases ⟨1, rfl⟩ (fun j => (Nat.not_lt_zero _ j.isLt).elim) i

inductive Site where
  | preheader
  | header

def terminators : Site → Terminator Opcode
  | .preheader => .br 0 (PhiView.packTerm entryArgs)
  | .header => .case (.var 2) (.br 0 (PhiView.packTerm backedgeArgs))
      (.br 1 (PhiView.packTerm exitArgs))

def sourceTyping : PhiView.SourceTyping (τ := Silmaril.Ty Unit) terminators where
  context
    | .preheader => wordCode :: inputContext
    | .header => afterHeader
  cases
    | .preheader => .jump
    | .header => .case (A := .unit) (B := .unit) (.var (i := 2) rfl) .jump .jump

def parameters : Nat → List (Silmaril.Ty Unit)
  | 0 => [wordCode, wordCode, wordCode]
  | 1 => [wordCode]
  | _ + 2 => []

def blockArgs : PhiView.BlockArgs sourceTyping parameters
  | ⟨.preheader, .jump⟩ => ⟨entryArgs, rfl⟩
  | ⟨.header, .left .jump⟩ => ⟨backedgeArgs, rfl⟩
  | ⟨.header, .right .jump⟩ => ⟨exitArgs, rfl⟩

def phiView : PhiView.View sourceTyping parameters := PhiView.ofBlockArgs blockArgs

def edge : Incoming → PhiView.EdgeOcc terminators
  | .entry => ⟨.preheader, .jump⟩
  | .backedge => ⟨.header, .left .jump⟩

/-- The environment is already at the selected terminator leaf. -/
def latchPayload (arrival : Incoming) (old : Env (Word m)) : Value (Word m) :=
  match arrival with
  | .entry => .pair (old 2) (.pair (old 3) (.pair (old 0) .unit))
  | .backedge => .pair (old 7) (.pair (old 9) (.pair (old 2) .unit))

def asRegion : Terminator Opcode → Region Opcode
  | .br label arg => .br label arg
  | .case discr l r => .case discr (asRegion l) (asRegion r)

def entry : Region Opcode := .let₁ (.op .seed .unit) (asRegion (terminators .preheader))

/-- Three tuple destructurings, then one let per header producer in graph
order. The true branch sends the whole new tuple back to local label zero. -/
def header : Region Opcode :=
  .let₂ (.var 0) (.let₂ (.var 0) (.let₂ (.var 0)
    (.let₁ (.op .test (.pair (.var 1) (.pair (.var 7) .unit)))
      (.let₁ (.op .advance (.pair (.var 2) .unit))
        (.let₁ (.op .observe (.pair (.var 7) (.pair (.var 5) .unit)))
          (asRegion (terminators .header)))))))

def blocks : Fin 1 → Region Opcode := fun _ => header

def lower : Region Opcode := .cfg entry 1 blocks

end Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
