import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- The evenness indicator appearing in the `d = 2` correction term. -/
def finite_rh_sqrt_resonance_general_even_indicator (n : ℕ) : ℝ :=
  if 2 ∣ n then 1 else 0

/-- Concrete audited data for the square-root-resonance expansion of the primitive count. -/
structure finite_rh_sqrt_resonance_general_data where
  n : ℕ
  lambda : ℝ
  R : ℝ
  Λ : ℝ
  criticalPhaseSum : ℝ
  primitiveCount : ℝ
  traceSubcriticalError : ℝ
  mobiusHalfContribution : ℝ
  divisorTail : ℝ
  lambda_gt_one : 1 < lambda
  Lambda_nonneg : 0 ≤ Λ
  R_le_Lambda : R ≤ Λ
  lambda_third_le_Lambda : lambda ^ (1 : ℕ) ≤ Λ ^ (3 : ℕ)
  np_primitive_count_eq :
    (n : ℝ) * primitiveCount =
      lambda ^ n + lambda ^ (n / 2) * criticalPhaseSum + traceSubcriticalError -
        mobiusHalfContribution + divisorTail
  traceSubcriticalError_bound : |traceSubcriticalError| ≤ Λ ^ n
  mobiusHalfContribution_bound :
    |mobiusHalfContribution -
        finite_rh_sqrt_resonance_general_even_indicator n * lambda ^ (n / 2)| ≤ Λ ^ n
  divisorTail_bound : |divisorTail| ≤ Λ ^ n

/-- Quantitative square-root-resonance statement for the audited primitive-count package. -/
def finite_rh_sqrt_resonance_general_statement
    (D : finite_rh_sqrt_resonance_general_data) : Prop :=
  |(D.n : ℝ) * D.primitiveCount -
      (D.lambda ^ D.n +
        D.lambda ^ (D.n / 2) *
          (D.criticalPhaseSum - finite_rh_sqrt_resonance_general_even_indicator D.n))| ≤
    3 * D.Λ ^ D.n

/-- Paper label: `prop:finite-rh-sqrt-resonance-general`. -/
theorem paper_finite_rh_sqrt_resonance_general
    (D : finite_rh_sqrt_resonance_general_data) :
    finite_rh_sqrt_resonance_general_statement D := by
  let η : ℝ := finite_rh_sqrt_resonance_general_even_indicator D.n
  have hsplit :
      (D.n : ℝ) * D.primitiveCount -
          (D.lambda ^ D.n + D.lambda ^ (D.n / 2) * (D.criticalPhaseSum - η)) =
        D.traceSubcriticalError + D.divisorTail -
          (D.mobiusHalfContribution - η * D.lambda ^ (D.n / 2)) := by
    rw [D.np_primitive_count_eq]
    ring
  have hΛ : 0 ≤ D.Λ ^ D.n := by
    exact pow_nonneg D.Lambda_nonneg _
  calc
    |(D.n : ℝ) * D.primitiveCount -
        (D.lambda ^ D.n + D.lambda ^ (D.n / 2) * (D.criticalPhaseSum - η))|
      = |(D.traceSubcriticalError + D.divisorTail) +
          -(D.mobiusHalfContribution - η * D.lambda ^ (D.n / 2))| := by
            rw [hsplit]
            ring_nf
    _ ≤ |D.traceSubcriticalError + D.divisorTail| +
          |-(D.mobiusHalfContribution - η * D.lambda ^ (D.n / 2))| := by
            exact abs_add_le _ _
    _ = |D.traceSubcriticalError + D.divisorTail| +
          |D.mobiusHalfContribution - η * D.lambda ^ (D.n / 2)| := by
            rw [abs_neg]
    _ ≤ (|D.traceSubcriticalError| + |D.divisorTail|) +
          |D.mobiusHalfContribution - η * D.lambda ^ (D.n / 2)| := by
            gcongr
            exact abs_add_le _ _
    _ ≤ (D.Λ ^ D.n + D.Λ ^ D.n) + D.Λ ^ D.n := by
            nlinarith [D.traceSubcriticalError_bound, D.divisorTail_bound,
              D.mobiusHalfContribution_bound]
    _ = 3 * D.Λ ^ D.n := by
      ring

end Omega.SyncKernelRealInput
