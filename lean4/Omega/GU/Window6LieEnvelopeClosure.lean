import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic

namespace Omega.GU

open Submodule

section LieClosureTermination

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Minimal bracket-closure predicate for a linear subspace. -/
def BracketClosed (bracket : V → V → V) (W : Submodule K V) : Prop :=
  ∀ ⦃x y : V⦄, x ∈ W → y ∈ W → bracket x y ∈ W

/-- Paper-facing finite-dimensional stabilization theorem for an iterative Lie-closure chain.
    Once the subspace chain is monotone, contained in the ambient finite-dimensional space, and
    any stabilized stage is known to be bracket-closed and minimal among bracket-closed subspaces
    containing the generators, the iteration terminates at the minimal Lie closure.
    prop:finite-dim-lie-closure-termination -/
theorem paper_window6_finite_dim_lie_closure_termination
    (bracket : V → V → V) (generators lieClosure : Submodule K V) (stage : ℕ → Submodule K V)
    (hzero : stage 0 = generators) (hmono : Monotone stage)
    (hupper : ∀ n, stage n ≤ lieClosure)
    (hstable_closed : ∀ n, stage n = stage (n + 1) → BracketClosed bracket (stage n))
    (_hminimal : generators ≤ lieClosure)
    (hleast :
      ∀ W : Submodule K V, generators ≤ W → BracketClosed bracket W → lieClosure ≤ W) :
    ∃ N, stage N = stage (N + 1) ∧ stage N = lieClosure := by
  let chain : ℕ →o Submodule K V := ⟨stage, hmono⟩
  obtain ⟨N, hstab⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance chain
  have hNN1 : stage N = stage (N + 1) := hstab (N + 1) (Nat.le_succ N)
  have hgen_stage : generators ≤ stage N := by
    rw [← hzero]
    exact hmono (Nat.zero_le N)
  have hclosedN : BracketClosed bracket (stage N) := hstable_closed N hNN1
  have hclosure_le : lieClosure ≤ stage N := hleast (stage N) hgen_stage hclosedN
  have hstage_le : stage N ≤ lieClosure := hupper N
  exact ⟨N, hNN1, le_antisymm hstage_le hclosure_le⟩

end LieClosureTermination

end Omega.GU
