module

public section

namespace Silmaril.Wasm.Profiles

inductive Wasm1
inductive Wasm2
inductive Wasm3
inductive Lime
inductive FX

/-- Core with no memories, tables or globals, allowing mutable GC and exceptions. -/
inductive Functional

/-- Closed functional Core with immutable GC fields, no GC writes and no exceptions. -/
inductive Strict

end Silmaril.Wasm.Profiles
