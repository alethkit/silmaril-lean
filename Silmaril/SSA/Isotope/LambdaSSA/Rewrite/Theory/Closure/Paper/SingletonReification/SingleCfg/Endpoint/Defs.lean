module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Assembly.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.CapturedSquare.Defs

/-! # Moving a captured input into the state of one local block -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg

open CfgEta.Uniformity (localMap)
open Silmaril.DeBruijn (lift)

universe u v

variable {Φ : Type v}

/-- Pair the original capture with the current local state. -/
def capturePair : Tm Φ := .pair (.var 1) (.var 0)

/-- Embed repeat payloads, taking the capture from the old block's environment. -/
def carryRepeat : Nat → Region Φ :=
  liftLSubstVars (localMap capturePair)

/-- Recover the original capture and state from the packed state and run
the block. Each repeat supplies a new state with the same capture. -/
def carryBlock (p : Region Φ) : Region Φ :=
  Paper.BoundSimulation.CapturedSquare.packedStep p

/-- A repeat from the initial entry can use the original singleton input. -/
def carryEntry (e : Region Φ) : Region Φ :=
  e.lsubst (localMap capturePair)

/-- Weaken a carried block past the original input of the outer CFG. -/
def carryBlockInCfg (p : Region Φ) : Region Φ :=
  (carryBlock p).renameVars (lift Nat.succ)

/-- Select an independent carried loop on repeat, or forward the outward
payload. The dispatcher itself is still at the original entry's context. -/
def carriedDispatch {τ : Type u} (P : τ) (q : Region Φ) : Nat → Region Φ
  | 0 => (feedbackRegion [P] (fun _ => q) 0).renameVars (lift Nat.succ)
  | i + 1 => .br i (.var 0)

/-- One continuation on the packed source exit for the carried version of
the original CFG. -/
def carriedExitContinuation {τ : Type u} [TypeFormers τ] (X S D : τ) (b : Region Φ) :
    Region Φ :=
  let P := Silmaril.product X S
  let q := carryBlock (decodeExits (Paper.PackedBody.applyPacked b) [S, D])
  compLSubst (fun _ => unpackExits [S, D])
    (compLSubst (localMap capturePair) (carriedDispatch P q)) 0

/-- One continuation on the packed source exit for the canonical region. -/
def canonicalExitContinuation {τ : Type u} [TypeFormers τ] (X S : τ) (step : Region Φ) :
    Region Φ :=
  let drop : Region Φ := .let₂ (.var 0) (.br 0 (.var 0))
  let loop := SyntacticCategory.iterateRegion (Silmaril.product X S) step
  let done := Paper.PackedBody.applyPacked drop
  let again := Paper.PackedBody.applyPacked (loop.lsubst (fun _ => drop.renameVars (lift Nat.succ)))
  compLSubst (fun _ => (exitDecoder (τ := τ)).renameVars (lift Nat.succ))
    (fun _ => Paper.RetainedCase.boundCase done again) 0

end Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.SingleCfg
