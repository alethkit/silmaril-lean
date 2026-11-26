module

import Silmaril.SSA.MLIR.Module.Symbols.Thms
import Silmaril.SSA.MLIR.Arith.Examples.Defs
import Silmaril.SSA.MLIR.Institution.Arith.Defs

/-! A forward call in a typed body, with a profile-preserving arithmetic translation. -/

namespace Silmaril.MLIR.Module.Symbols.Examples

open Arith (Block Width)
open Arith.Examples (i1 i8 squareAdd)
open Institution.Arith (signature translate)

private def declared : Module (FuncSignature (List Width) Width) where
  funcs := [("entry", ⟨[i1, i8], i8⟩), ("callee", ⟨[i1, i8], i8⟩)]
  uniqueNames := by decide

/-- The call form passes the block arguments in order and returns the call result. -/
private inductive Body (Local : List Width → Width → Type) : List Width → Width → Type where
  | localBlock {inputs output} : Local inputs output → Body Local inputs output
  | callAndReturn {inputs output} : DirectCall declared inputs output → Body Local inputs output

private def forwardCall : DirectCall declared [i1, i8] i8 :=
  (DirectCall.resolve? declared "callee" [i1, i8] i8).get (by decide)

private def source : FuncModule (Body Block) where
  funcs := [("entry", ⟨[i1, i8], i8, .callAndReturn forwardCall⟩),
            ("callee", ⟨[i1, i8], i8, .localBlock squareAdd⟩)]
  uniqueNames := declared.uniqueNames

private abbrev IsolatedBody (inputs : List Width) (output : Width) :=
  Institution.Block signature inputs.get (fun _ : Fin 1 => output)

private def translateBody {inputs output} : Body Block inputs output →
    Body IsolatedBody inputs output
  | .localBlock block => .localBlock (fun _ => translate block)
  | .callAndReturn call => .callAndReturn call

private def target : FuncModule (Body IsolatedBody) := source.map id id translateBody

-- Check the environment used to type the body against the actual module's declarations.
private theorem source_signatures : source.signatures = declared := rfl

example : target.signatures = declared :=
  (source.signatures_map translateBody).trans source_signatures

example : target.funcs.map Prod.fst = ["entry", "callee"] := rfl

example : (DirectCall.resolve? source.signatures "callee" [i1, i8] i8).map DirectCall.callee =
    some "callee" := rfl

example : DirectCall.resolve? source.signatures "missing" [i1, i8] i8 = none := rfl

example : DirectCall.resolve? source.signatures "callee" [i8, i1] i8 = none := rfl

example : DirectCall.resolve? source.signatures "callee" [i1, i8] i1 = none := rfl

example : HEq (DirectCall.resolve? target.signatures "callee" [i1, i8] i8)
    (some forwardCall) := source.resolveDirectCall?_map translateBody "callee" [i1, i8] i8

end Silmaril.MLIR.Module.Symbols.Examples
