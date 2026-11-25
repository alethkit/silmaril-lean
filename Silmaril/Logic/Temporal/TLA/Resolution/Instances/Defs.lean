module

public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs

/-! Name, arity and level checking for first-order TLA+ module instances. -/

public section

namespace Silmaril.Logic.Temporal.TLA.Resolution.Instances

inductive Diagnostic where
  | resolution (error : Resolution.Diagnostic)
  | levels (error : Levels.Diagnostic)
  deriving Repr

structure CheckedInstances where
  private mk ::
  registry : CheckedRegistry
  levels : Levels.CheckedLevels

/-- Recover a checked instance environment and the member's home binding.
An anonymous reuse with no substitutions already points directly at its home. -/
def CheckedInstances.memberAt (checked : CheckedInstances) (id : BindingId) :
    Option (InstancePlan × InstanceMember) :=
  checked.registry.instanceMemberAt id

/-- Find the plan for a particular INSTANCE declaration in its host module. -/
def CheckedInstances.instanceAt (checked : CheckedInstances) (site : Site) : Option InstancePlan :=
  (checked.registry.moduleAt site.moduleId).bind (·.instanceAt site.path)

/-- Check the entire reachable graph, including every WITH replacement. -/
def check (registry : Registry) (root : ModuleId) (external : Levels.ExternalLevels := []) :
    Except Diagnostic CheckedInstances := do
  let resolved ← (resolveWith .instanceSyntax registry root).mapError .resolution
  let levels ← (Levels.check resolved external).mapError .levels
  return ⟨resolved, levels⟩

end Silmaril.Logic.Temporal.TLA.Resolution.Instances
