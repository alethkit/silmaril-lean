module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Blocks.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Proofs

open Diamond (Model Ty ValueSort dataPorts sortValue)
open RVSDG (Wires)
open Join (Block)
open Blocks (Bank)
open SeaOfNodes.Loop (Graph)

universe u v w

variable {Data : Type u} {Op : Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {header site entry : Fin size}

theorem outgoing_eq {args : List (Ty Data)} {past : List (List (Ty Data))}
    (path : Path src header site) (current : Wires args past (dataPorts regs)) :
    (CFG.compileBlock path.quads current).outgoing = path.outgoing current := by
  induction path generalizing past with
  | latch => rfl
  | jump site _ rest ih =>
    let next := (CFG.compileBlock (src site).body current).outgoing
    have fused := compile_append_outgoing (src site).body rest.quads current
    have transport : HEq ((Path.jump site ‹_› rest).outgoing current) (rest.outgoing next) := by
      change HEq (cast _ (rest.outgoing next)) (rest.outgoing next)
      exact cast_heq _ _
    exact eq_of_heq ((fused.trans (heq_of_eq (ih next))).trans transport.symm)

theorem length_pos (path : Path src header site) : 0 < path.blocks.length := by
  cases path <;> simp [Path.blocks]

theorem latch_mem (path : Path src header site) : path.latchBlock ∈ path.blocks := by
  induction path <;> simp_all [Path.latchBlock, Path.blocks]

variable (m : Model.{u, v, w} Op)

private theorem run_activation (path : Path src header site) (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + path.blocks.length) site old =
      let next := path.quads.eval m old
      if (next.get path.test).down then src.runFrom m fuel header next
      else some (next.get path.result) := by
  induction path generalizing old with
  | latch site test result edge =>
    simp only [Path.blocks, List.length_cons, List.length_nil, Nat.zero_add,
      Source.runFrom, edge, Terminator.select, Path.quads, Path.test, Path.result]
    by_cases taken : (((src site).body.eval m old).get test).down = true <;> simp [taken]
  | jump site edge rest ih =>
    simp only [Path.blocks, List.length_cons, Nat.add_succ, Source.runFrom, edge, Terminator.select,
      Path.quads, Path.test, Path.result, Block.eval, List.foldl_append]
    exact ih ((src site).body.eval m old)

private theorem short_activation (path : Path src header site) (fuel : Nat) (old : Bank (regs := regs) m)
    (short : fuel < path.blocks.length) : src.runFrom m fuel site old = none := by
  induction path generalizing fuel old with
  | latch =>
    have zero : fuel = 0 := by simpa [Path.blocks] using short
    subst fuel
    rfl
  | jump site edge rest ih =>
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [Source.runFrom, edge, Terminator.select]
      exact ih fuel ((src site).body.eval m old) (by simpa [Path.blocks] using short)

variable (p : Program src entry)

private theorem run_step (fuel : Nat) (old : Bank (regs := regs) m) :
    src.runFrom m (fuel + p.activationLength) p.header old =
      match p.fuse.step m old with
      | .inl result => some result
      | .inr next => src.runFrom m fuel p.header next := by
  rw [Program.activationLength, run_activation m p.activation]
  simp only [Blocks.Program.step, Program.fuse]
  by_cases taken : ((p.activation.quads.eval m old).get p.activation.test).down = true <;> simp [taken]

private theorem run_from_budget (budget extra : Nat) (short : extra < p.activationLength)
    (old : Bank (regs := regs) m) :
    src.runFrom m (extra + p.activationLength * (budget + 1)) p.header old =
      p.fuse.evalFrom m budget old := by
  induction budget generalizing old with
  | zero =>
    rw [Nat.mul_one, run_step m p, Blocks.Program.evalFrom]
    cases p.fuse.step m old with
    | inl _ => rfl
    | inr next => exact short_activation m p.activation extra next short
  | succ budget ih =>
    rw [Nat.mul_succ p.activationLength (budget + 1), ← Nat.add_assoc,
      run_step m p, Blocks.Program.evalFrom]
    cases p.fuse.step m old with
    | inl _ => rfl
    | inr next => exact ih next

variable (input : Bank (regs := regs) m)

theorem lower_budget (budget extra : Nat) (short : extra < p.activationLength) :
    src.runFrom m (extra + p.activationLength * (budget + 1) + 1) entry input =
      p.lower.evalBackedges m budget input := by
  simp only [Source.runFrom, p.entryJump, Terminator.select]
  exact (run_from_budget m p budget extra short ((src entry).body.eval m input)).trans
    (p.fuse.lower_evalBackedges m input budget).symm

theorem lower_run (fuel : Nat) :
    src.runFrom m fuel entry input =
      if p.activationLength + 1 ≤ fuel then
        p.lower.evalBackedges m ((fuel - (p.activationLength + 1)) / p.activationLength) input
      else none := by
  by_cases enough : p.activationLength + 1 ≤ fuel
  · rw [ite_eq_left enough]
    let surplus := fuel - (p.activationLength + 1)
    have split := Nat.mod_add_div surplus p.activationLength
    have balance := Nat.sub_add_cancel enough
    have fuel_eq : fuel = surplus % p.activationLength +
        p.activationLength * (surplus / p.activationLength + 1) + 1 := by
      rw [Nat.mul_succ]
      omega
    conv_lhs => rw [fuel_eq]
    exact lower_budget m p input (surplus / p.activationLength) (surplus % p.activationLength)
      (Nat.mod_lt _ (length_pos p.activation))
  · rw [ite_eq_right enough]
    cases fuel with
    | zero => rfl
    | succ fuel =>
      simp only [Source.runFrom, p.entryJump, Terminator.select]
      exact short_activation m p.activation fuel ((src entry).body.eval m input) (by
        unfold Program.activationLength at enough
        omega)

theorem returns_iff (result : sortValue m.value out) :
    p.lower.Returns m input result ↔ ∃ fuel, src.runFrom m fuel entry input = some result := by
  rw [Graph.returns_iff_evalBackedges]
  constructor
  · rintro ⟨budget, run⟩
    exact ⟨0 + p.activationLength * (budget + 1) + 1,
      (lower_budget m p input budget 0 (length_pos p.activation)).trans run⟩
  · rintro ⟨fuel, run⟩
    rw [lower_run] at run
    split at run
    · exact ⟨_, run⟩
    · contradiction

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Chain.Proofs
