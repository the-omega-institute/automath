import Omega.GU.Window6LieEnvelopeClosure

namespace Omega.GU

open Submodule

section LieClosureTermination

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Chapter-facing restatement of the finite-dimensional Lie-closure stabilization theorem.
    prop:finite-dim-lie-closure-termination -/
theorem paper_finite_dim_lie_closure_termination
    (bracket : V → V → V) (generators lieClosure : Submodule K V) (stage : ℕ → Submodule K V)
    (hzero : stage 0 = generators) (hmono : Monotone stage)
    (hupper : ∀ n, stage n ≤ lieClosure)
    (hstable_closed : ∀ n, stage n = stage (n + 1) → BracketClosed bracket (stage n))
    (hminimal : generators ≤ lieClosure)
    (hleast :
      ∀ W : Submodule K V, generators ≤ W → BracketClosed bracket W → lieClosure ≤ W) :
    ∃ N, stage N = stage (N + 1) ∧ stage N = lieClosure := by
  exact paper_window6_finite_dim_lie_closure_termination
    bracket generators lieClosure stage hzero hmono hupper hstable_closed hminimal hleast

end LieClosureTermination

end Omega.GU
