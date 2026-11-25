module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Semantics.Operational.Policy.Defs
public import Silmaril.Wasm.Institution.Operational.Thms

/-!
# Ground SOS rules for flat Core integer division

The instruction guard admits values, both widths and signs of integer division,
`nop`, and a pending or final trap. It is an operational support check. It
admits, for example, division lacking operands, which can get stuck. The
rules preserve the store and frame. Sequence contexts have a value prefix and
an admitted continuation. Trap propagation may discard just part of that
context, as in Core's small-step relation.

The rule families follow `Step_pure/binop-val`, `binop-trap`, `nop`,
`trap-instrs` and `Step/ctxt-instrs` in WebAssembly Core 3.0, together with
the partial `idiv_` operator at signed and unsigned interpretations.
See `webassembly-core-3` in
`references.bib` and the upstream pin in `specs/wasm/core-3.0.json`.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Division

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Semantics.Operational (WithUB)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

def divOp (t : IntType) (sign : Signedness) : Admin :=
  .plain (.intBinOp t (.div sign))

abbrev intConst (t : IntType) (x : IntValue t) : Admin :=
  .plain (.intConst t x)

def quotient (t : IntType) (sign : Signedness) (x y : IntValue t) : IntValue t :=
  match sign with
  | .unsigned => x / y
  | .signed => x.sdiv y

abbrev Overflows (t : IntType) (sign : Signedness) (x y : IntValue t) : Prop :=
  sign = .signed ∧ x = BitVec.intMin t.width ∧ y = -1

inductive Allowed : Admin → Prop where
  | value (v : Val) : Allowed v.toAdmin
  | division (t : IntType) (sign : Signedness) : Allowed (divOp t sign)
  | nop : Allowed (.plain .nop)
  | trap : Allowed .trap

def AdmittedCode (code : List Admin) : Prop := ∀ a ∈ code, Allowed a

def Admitted {H : Type} (c : Config H) : Prop := AdmittedCode c.code

abbrev Judgment (H : Type) := Config H × Config H

def codeEdge {H : Type} (s : Store H) (f : Frame) (before after : List Admin) : Judgment H :=
  (⟨s, f, before⟩, ⟨s, f, after⟩)

/-- Each constructor instantiates one ground rule. Only the context rule
has a judgment premise. The other hypotheses are arithmetic or syntactic guards. -/
inductive RuleInstance (H : Type) : Rule (Judgment H) → Prop where
  | divide (s : Store H) (f : Frame) (t : IntType) (sign : Signedness) (x y : IntValue t)
      (nonzero : y ≠ 0) (noOverflow : ¬ Overflows t sign x y) :
      RuleInstance H ⟨[], codeEdge s f [intConst t x, intConst t y, divOp t sign]
        [intConst t (quotient t sign x y)]⟩
  | zero (s : Store H) (f : Frame) (t : IntType) (sign : Signedness) (x : IntValue t) :
      RuleInstance H ⟨[], codeEdge s f [intConst t x, intConst t 0, divOp t sign] [.trap]⟩
  | overflow (s : Store H) (f : Frame) (t : IntType) :
      RuleInstance H ⟨[], codeEdge s f
        [intConst t (BitVec.intMin t.width), intConst t (-1), divOp t .signed] [.trap]⟩
  | nop (s : Store H) (f : Frame) :
      RuleInstance H ⟨[], codeEdge s f [.plain .nop] []⟩
  | trap (s : Store H) (f : Frame) (vs : List Val) (rest : List Admin)
      (nonempty : vs ≠ [] ∨ rest ≠ []) (admitted : AdmittedCode rest) :
      RuleInstance H ⟨[], codeEdge s f (vals vs ++ [.trap] ++ rest) [.trap]⟩
  | context (s : Store H) (f : Frame) (vs : List Val) (before after rest : List Admin)
      (nonempty : vs ≠ [] ∨ rest ≠ []) (admitted : AdmittedCode rest) :
      RuleInstance H ⟨[codeEdge s f before after],
        codeEdge s f (vals vs ++ before ++ rest) (vals vs ++ after ++ rest)⟩

/-- Core configurations and unit-labelled edges, with no auxiliary judgments. -/
def shape (H : Type) : SOS.Shape.{0} := ⟨⟨Config H, Unit⟩, Judgment H, fun (s, _, t) => (s, t)⟩

def presentation (H : Type) : Presentation :=
  ⟨shape H, {r | RuleInstance H r}⟩

abbrev DerivesEdge {H : Type} (s t : Config H) : Prop := (presentation H).Derives (s, t)

abbrev transitionSystem (H : Type) : TransitionSystem :=
  Presentation.toTransitionSystems.obj (presentation H)

/-- An optional boundary policy marks out-of-slice code as unsupported.
An admitted terminal trap is a defined observation. -/
def policy (H : Type) : WithUB (Config H) (List Val) where
  step := DerivesEdge
  observe c o := Admitted c ∧ match o with
    | .returned vs => c.code = vals vs
    | .trap => c.code = [.trap]
  ub c := ¬ Admitted c

end Silmaril.Wasm.Institution.Operational.Division
