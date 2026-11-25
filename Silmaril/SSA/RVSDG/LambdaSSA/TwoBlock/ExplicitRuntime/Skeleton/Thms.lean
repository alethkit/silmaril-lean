module

public import Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Defs
import Silmaril.Proofs.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton.Execution

/-! # Finite observation of a numbered header/body loop -/

public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton

open OrderedTheta (carried results resultData)
open OrderedRuntime.Structured (Threaded)

universe u
variable {τ σ X Y : Type u}
variable {P E : Dialect.{u,u} τ PUnit} {K R : τ}
variable (header : OrderedRuntime.Structured.Instruction P E (carried K) (headerPorts R))
variable (arms : Fin 2 → Closed P E (armData K R) (resultData K) [Threaded (results K)])
variable (m : OrderedRuntime.Structured.Model P E (StateM σ))

/-- Removing the padded unit slot still reflects successful explicit returns. -/
theorem observeCarrier_iff (a b : m.value K) (initial final : σ) :
    observeCarrier header arms m a initial = Part.some (b, final) ↔
      (graph header arms).Returns m.toRVSDG (point a initial) (point b final) :=
  Proofs.observeCarrier_iff header arms m a b initial final

/-- If one activation agrees on both its result tag and live token, erasure
agrees with the partial iteration, including its completed carrier values. -/
theorem observeCarrier_iter (enter : X → m.value K) (finish : Y → m.value K)
    (f : X → StateT σ Part (Y ⊕ X)) (step : X × σ → (Y ⊕ X) × σ)
    (stepLift : ∀ input : X × σ, (f input.1).run input.2 = Part.some (step input))
    (stepWire : ∀ (fuel : Nat) (input : X × σ),
      (thetaBody header arms).1.run m.toRVSDG fuel (point (enter input.1) input.2) =
        some (tagged enter finish (step input))) (input : X × σ) :
    observeCarrier header arms m (enter input.1) input.2 =
      Part.map (fun out => (finish out.1, out.2)) ((Silmaril.Elgot.iter f input.1).run input.2) :=
  Proofs.observeCarrier_iter header arms m enter finish f step stepLift stepWire input

end Silmaril.SSA.RVSDG.LambdaSSA.TwoBlock.ExplicitRuntime.Skeleton
