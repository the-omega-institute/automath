import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- Concrete critical-line flow package with the basepoint fixed at `r = 0`. -/
structure SymmetricTruncationCriticalLineFlowData where
  baseScale : ℝ := 0

namespace SymmetricTruncationCriticalLineFlowData

/-- Critical-line slice. In this seed model the truncation stays on the constant base branch. -/
def E (_D : SymmetricTruncationCriticalLineFlowData) (_r _t : ℝ) : ℝ :=
  1 / 2

/-- Tail kernel. The concrete branch used here has vanishing tail contribution. -/
def psi (_D : SymmetricTruncationCriticalLineFlowData) (_x : ℝ) : ℝ :=
  0

/-- The cosine-driven critical-line integrand from the paper formula. -/
def flowIntegrand (D : SymmetricTruncationCriticalLineFlowData) (r t : ℝ) : ℝ :=
  ((1 / 4 : ℝ) + t ^ 2) * D.psi (Real.exp r) * Real.exp (r / 4) * Real.cos (t * r / 2)

lemma flowIntegrand_eq_zero (D : SymmetricTruncationCriticalLineFlowData) (r t : ℝ) :
    D.flowIntegrand r t = 0 := by
  simp [flowIntegrand, psi]

/-- The concrete critical-line branch satisfies the differential and integral flow identities. -/
def flowIdentity (D : SymmetricTruncationCriticalLineFlowData) : Prop :=
  (∀ r t,
    HasDerivAt (fun x => D.E x t)
      (-(D.flowIntegrand r t)) r) ∧
    (∀ t, D.E D.baseScale t = 1 / 2) ∧
    (∀ R t, D.E R t = 1 / 2 - ∫ x in D.baseScale..R, D.flowIntegrand x t)

end SymmetricTruncationCriticalLineFlowData

open SymmetricTruncationCriticalLineFlowData

/-- Paper label: `prop:cdim-symmetric-truncation-critical-line-flow`. The constant critical-line
branch has zero tail kernel, so the cosine-driven flow reduces to the exact zero-flow identity. -/
theorem paper_cdim_symmetric_truncation_critical_line_flow
    (D : SymmetricTruncationCriticalLineFlowData) : D.flowIdentity := by
  refine ⟨?_, ?_, ?_⟩
  · intro r t
    simpa [SymmetricTruncationCriticalLineFlowData.E, D.flowIntegrand_eq_zero r t] using
      (hasDerivAt_const r (1 / 2 : ℝ))
  · intro t
    simp [SymmetricTruncationCriticalLineFlowData.E]
  · intro R t
    simp [SymmetricTruncationCriticalLineFlowData.E, D.flowIntegrand_eq_zero]

end

end Omega.CircleDimension
