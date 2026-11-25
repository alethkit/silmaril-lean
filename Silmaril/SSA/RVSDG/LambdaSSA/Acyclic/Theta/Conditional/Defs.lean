module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.ExplicitRuntime.Defs

/-! # A flat LambdaSSA CFG whose entry may bypass a loop -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional

open Isotope.LambdaSSA (Region)
open LinearChain (Site localSite externalSite)
open LinearChain.Wiring (newest)
open OrderedTheta (carried results carriedData resultData)
open OrderedRuntime.Structured (Threaded runtimePort nextRuntime)
open NestedTheta.ExplicitRuntime (EntryChecked)
open TwoBlock.TwoExit (Carrier)
open ExplicitRuntime (Op)

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A L B K E D : τ}

/-- The entry classifier either supplies a typed external result or enters
the existing loop with its typed payload. Feedback is internal to that loop. -/
structure Guarded (Φ : Type u) [HasTy Φ τ] (A L B K E D : τ) where
  gate : TwoBlock.Instruction Φ A (Carrier L E D)
  loop : Loop Φ L B K E D

variable (s : Guarded Φ A L B K E D)

def enterLoop : Site (Theta.Labels s.loop) L :=
  localSite (Theta.localTypes s.loop) [E,D] 0

def firstExit : Site (Theta.Labels s.loop) E :=
  externalSite (Theta.localTypes s.loop) [E,D] 0

def secondExit : Site (Theta.Labels s.loop) D :=
  externalSite (Theta.localTypes s.loop) [E,D] 1

/-- The only local entry edge targets the loop header. The other branches
retain the CFG's two actual external labels. -/
def entry : Region Φ :=
  .case (.op s.gate.op (.var 0))
    (.case (.var 0) (.br (firstExit s).index (.var 0)) (.br (secondExit s).index (.var 0)))
    (.br (enterLoop s).index (.var 0))

theorem entryTyping : Region.HasType [A] (entry s) (Theta.Labels s.loop) :=
  .case (s.gate.typing [])
    (.case (.var rfl) (.br (firstExit s).typing (.var rfl)) (.br (secondExit s).typing (.var rfl)))
    (.br (enterLoop s).typing (.var rfl))

def region : Region Φ :=
  .cfg (entry s) (bodyCount s.loop + 2) (fun i => (Theta.blockAt s.loop i).region)

theorem regionTyping : Region.HasType [A] (region s) [E,D] :=
  .cfg (Theta.localTypes s.loop) (entryTyping s) (fun i => (Theta.blockAt s.loop i).typing [A])

abbrev Signatures (L E D : τ) :=
  [Threaded (results (Carrier L E D)), Threaded (carried (Carrier L E D))]

abbrev Graph (Φ : Type u) [HasTy Φ τ] (A L E D : τ) :=
  NestedTheta.Graph (Op Φ) (Threaded (carried A)) [] (Signatures L E D)
    (Threaded (carried (Carrier L E D)))

namespace Wiring

open ExplicitRuntime.Wiring (Code primitive choice finish)

abbrev arm (s : Guarded Φ A L B K E D) :
    Code (past := []) Φ (carriedData (Carrier L E D)) (carriedData (Carrier L E D))
      (.arg (runtimePort (carried (Carrier L E D)))) :=
  ⟨_, (ExplicitRuntime.Wiring.loop s.loop).1, (ExplicitRuntime.Wiring.loop s.loop).2⟩

/-- Emit one classifier and one forward γ. The right arm uses the existing
numbered θ term, including its original admission witness. -/
def openCode : Code (past := []) Φ (carriedData A) (carriedData (Carrier L E D))
    (.arg (runtimePort (carried A))) :=
  let ports := results (Carrier L E D)
  let saved := [Threaded ports]
  let bypass := finish (Φ := Φ) (a := carriedData (Carrier L E D)) [] (.arg _) (.arg .head)
  let select := choice (carriedData _) (carriedData _) bypass (arm s)
    (newest .head []) (nextRuntime [] ports) (.cons (newest (.tail .head) []) .nil)
    (finish (a := carriedData A) (saved ++ [Threaded (carried (Carrier L E D))])
      (nextRuntime saved _) (newest .head saved))
  primitive (carriedData A) (resultData _) (.effect (.acyclic (.classify .direct s.gate)))
    (.arg (runtimePort (carried A))) (.cons (.arg .head) .nil) select

def code : Σ t : NestedTheta.Term (Op Φ) (Threaded (carried A)) [] (Signatures L E D)
    (Threaded (carried (Carrier L E D))),
    EntryChecked (a := carriedData A) (b := carriedData (Carrier L E D)) t :=
  (openCode s).2

end Wiring

def graph : Graph Φ A L E D := (Wiring.code s).1.toGraph

def graphChecked : EntryChecked (a := carriedData A) (b := carriedData (Carrier L E D)) (graph s).toTerm :=
  (Wiring.code s).2.collect

inductive Source (A L B K E D : τ) : Region Φ → Type u where
  | guarded (s : Guarded Φ A L B K E D) : Source A L B K E D (region s)

inductive Related (A L B K E D : τ) : Region Φ → Graph Φ A L E D → Type u where
  | guarded (s : Guarded Φ A L B K E D) : Related A L B K E D (region s) (graph s)

def lower {r : Region Φ} (source : Source A L B K E D r) :
    Σ g : Graph Φ A L E D, Related A L B K E D r g :=
  match source with | .guarded s => ⟨graph s, .guarded s⟩

theorem Related.typing {r : Region Φ} {g : Graph Φ A L E D}
    (w : Related A L B K E D r g) : Region.HasType [A] r [E,D] :=
  match w with | .guarded s => regionTyping s

def Related.checked {r : Region Φ} {g : Graph Φ A L E D} (w : Related A L B K E D r g) :
    EntryChecked (a := carriedData A) (b := carriedData (Carrier L E D)) g.toTerm :=
  match w with | .guarded s => graphChecked s

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.Conditional
