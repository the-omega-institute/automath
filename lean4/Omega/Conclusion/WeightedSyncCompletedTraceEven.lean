import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

namespace Omega.Conclusion

/-- A concrete self-dual conjugation package for a weighted completed trace model. -/
structure SelfDualConjugation (n : Type*) [Fintype n] [DecidableEq n] where
  piMatrix : Matrix n n ℂ
  completedKernel : ℝ → Matrix n n ℂ
  pi_involutive : piMatrix * piMatrix = 1
  kernel_symmetry : ∀ θ : ℝ, completedKernel (-θ) = piMatrix * completedKernel θ * piMatrix

/-- The weighted completed trace attached to the kernel family. -/
noncomputable def completedTrace {n : Type*} [Fintype n] [DecidableEq n] (D : SelfDualConjugation n)
    (θ : ℝ) : ℂ :=
  Matrix.trace (D.completedKernel θ)

/-- The odd part of the completed trace. -/
noncomputable def completedTraceOddPart {n : Type*} [Fintype n] [DecidableEq n]
    (D : SelfDualConjugation n)
    (θ : ℝ) : ℂ :=
  completedTrace D θ - completedTrace D (-θ)

lemma completedTrace_neg_eq {n : Type*} [Fintype n] [DecidableEq n]
    (D : SelfDualConjugation n) (θ : ℝ) :
    completedTrace D (-θ) = completedTrace D θ := by
  unfold completedTrace
  rw [D.kernel_symmetry θ, Matrix.trace_mul_cycle, D.pi_involutive, one_mul]

/-- Self-dual conjugation makes the weighted completed trace even: `\widetilde B(θ)` and
`\widetilde B(-θ)` are similar through the involution `Π`, so the trace is unchanged and the odd
part vanishes identically.
    prop:conclusion-weighted-sync-completed-trace-even -/
theorem paper_conclusion_weighted_sync_completed_trace_even {n : Type*} [Fintype n]
    [DecidableEq n] (D : SelfDualConjugation n) :
    (∀ θ : ℝ, completedTrace D (-θ) = completedTrace D θ) ∧
      (∀ θ : ℝ, completedTraceOddPart D θ = 0) := by
  refine ⟨completedTrace_neg_eq D, ?_⟩
  intro θ
  unfold completedTraceOddPart
  rw [completedTrace_neg_eq D θ]
  ring

end Omega.Conclusion
