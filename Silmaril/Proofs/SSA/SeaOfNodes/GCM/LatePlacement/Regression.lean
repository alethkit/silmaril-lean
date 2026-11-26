module

import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example.Defs

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement.Regression

open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example

attribute [local cbv_eval] List.maxOn?_nil List.maxOn?_cons maxOn_eq_ite

-- The shared Phi destination is join, while the two reads are at left.
example : bounds = some (block .left, block .fork) := by cbv

example : (tree?.bind fun tree => resolveUses? tree.1 parallelUses) =
    some [(.phi (block .left) .onTrue 0, ⟨block .left, 1⟩),
      (.phi (block .left) .onFalse 0, ⟨block .left, 1⟩)] := by cbv

-- An ordinary read at the join joins the left Phi reads at the same fork.
example : (tree?.bind fun tree => lateBound? tree.1 blocks
    (.ordinary ⟨block .join, 0⟩ :: parallelUses)) = some (block .fork) := by cbv

-- Entry is a successful bound distinct from absence of a bound.
example : (tree?.bind fun tree => lateBound? tree.1 blocks
    (.ordinary ⟨none, 0⟩ :: bothArms)) = some none := by cbv

private def localUses : List (Use Label) := .ordinary ⟨block .left, 0⟩ :: parallelUses

example : (tree?.map fun tree =>
    (lateBound? tree.1 blocks localUses,
      checkPlacement tree.1 [] localUses ⟨block .left, 0⟩,
      checkPlacement tree.1 [] localUses ⟨block .left, 1⟩)) =
    some (some (block .left), true, false) := by cbv

private def invalidUses : List (List (Use Label)) :=
  [[], [.phi (block .left) .jump 0], [.phi (block .left) .onFalse 1],
    [.ordinary ⟨block .left, 2⟩], [.ordinary ⟨block .dead, 0⟩]]

example : (tree?.map fun tree => invalidUses.map (lateBound? tree.1 blocks)) =
    some [none, none, none, none, none] := by cbv

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LatePlacement.Regression
