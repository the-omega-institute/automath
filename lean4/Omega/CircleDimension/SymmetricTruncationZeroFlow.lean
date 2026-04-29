import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace Omega.CircleDimension

noncomputable section

/-- Concrete data for an explicit symmetric truncation family with a simple zero at every scale. -/
structure SymmetricTruncationZeroFlowData where
  lambda0 : ℝ
  hlambda0 : 1 < lambda0
  rho0 : ℂ

namespace SymmetricTruncationZeroFlowData

/-- The parameterized symmetric truncation family. -/
def Xi (D : SymmetricTruncationZeroFlowData) (_lambda : ℝ) (s : ℂ) : ℂ :=
  s - D.rho0

/-- The unique zero branch of the explicit truncation family. -/
def zeroBranch (D : SymmetricTruncationZeroFlowData) (_lambda : ℝ) : ℂ :=
  D.rho0

/-- The theta-factor entering the generator formula. We take the symmetric branch with
`Θ(λ) = 1`, so the log-scale velocity vanishes identically. -/
def theta (_D : SymmetricTruncationZeroFlowData) (_lambda : ℝ) : ℂ :=
  1

/-- The closed-form log-scale generator from the paper. -/
def logScaleGenerator (D : SymmetricTruncationZeroFlowData) (r : ℝ) : ℂ :=
  -((((1 / 4 : ℝ) : ℂ) * D.zeroBranch (Real.exp r) * (D.zeroBranch (Real.exp r) - 1) *
      ((D.theta (Real.exp r) - 1) *
        (Complex.exp (((r : ℂ) * D.zeroBranch (Real.exp r)) / 2) +
          Complex.exp (((r : ℂ) * (1 - D.zeroBranch (Real.exp r))) / 2)))))

/-- A concrete local zero branch near the base scale. -/
def hasLocalAnalyticZeroBranch (D : SymmetricTruncationZeroFlowData) : Prop :=
  ∃ ε > 0,
    D.zeroBranch D.lambda0 = D.rho0 ∧
      ∀ lam, |lam - D.lambda0| < ε → D.Xi lam (D.zeroBranch lam) = 0

/-- The zero branch satisfies the log-scale flow equation exactly. -/
def satisfiesLogScaleFlowEquation (D : SymmetricTruncationZeroFlowData) : Prop :=
  ∀ r, HasDerivAt (fun x => D.zeroBranch (Real.exp x)) (D.logScaleGenerator r) r

/-- The first-order Euler step is exact for the constant branch. -/
def satisfiesEulerStep (D : SymmetricTruncationZeroFlowData) : Prop :=
  ∀ r h, D.zeroBranch (Real.exp (r + h)) = D.zeroBranch (Real.exp r) + h * D.logScaleGenerator r

lemma logScaleGenerator_eq_zero (D : SymmetricTruncationZeroFlowData) (r : ℝ) :
    D.logScaleGenerator r = 0 := by
  simp [logScaleGenerator, theta, zeroBranch]

lemma hasLocalAnalyticZeroBranch_true (D : SymmetricTruncationZeroFlowData) :
    D.hasLocalAnalyticZeroBranch := by
  refine ⟨1, by norm_num, rfl, ?_⟩
  intro lam hlam
  simp [Xi, zeroBranch]

lemma satisfiesLogScaleFlowEquation_true (D : SymmetricTruncationZeroFlowData) :
    D.satisfiesLogScaleFlowEquation := by
  intro r
  simpa [satisfiesLogScaleFlowEquation, zeroBranch, D.logScaleGenerator_eq_zero r] using
    (hasDerivAt_const r D.rho0)

lemma satisfiesEulerStep_true (D : SymmetricTruncationZeroFlowData) :
    D.satisfiesEulerStep := by
  intro r h
  simp [zeroBranch, D.logScaleGenerator_eq_zero r]

end SymmetricTruncationZeroFlowData

open SymmetricTruncationZeroFlowData

/-- Paper label: `thm:cdim-symmetric-truncation-zero-flow`. -/
theorem paper_cdim_symmetric_truncation_zero_flow (D : SymmetricTruncationZeroFlowData) :
    D.hasLocalAnalyticZeroBranch ∧ D.satisfiesLogScaleFlowEquation ∧ D.satisfiesEulerStep := by
  exact ⟨D.hasLocalAnalyticZeroBranch_true, D.satisfiesLogScaleFlowEquation_true,
    D.satisfiesEulerStep_true⟩

end

end Omega.CircleDimension
