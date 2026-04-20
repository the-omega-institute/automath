import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Omega.Folding

open Matrix
open scoped BigOperators

/-- The Parry-normalized `4 × 4` gauge-anomaly kernel in the state order `(a,b,c,d)`. -/
def gaugeAnomalyJordanParryKernel : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ);
    0, 0, 1, 0;
    (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0;
    1, 0, 0, 0]

/-- The explicit quartic polynomial attached to the gauge-anomaly Parry kernel. -/
def gaugeAnomalyJordanSpectralPolynomial (μ : ℚ) : ℚ :=
  μ ^ 4 - (1 / 2 : ℚ) * μ ^ 3 - (3 / 4 : ℚ) * μ ^ 2 + (1 / 8 : ℚ) * μ + 1 / 8

/-- A scaled version of `P + (1/2)I`; its kernel is the `-1/2` eigenspace. -/
def gaugeAnomalyMinusHalfMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(4 : ℚ), 1, 0, 1;
    0, 2, 4, 0;
    2, 2, 2, 0;
    4, 0, 0, 2]

/-- The square of the scaled `-1/2` shift, written explicitly for exact kernel calculations. -/
def gaugeAnomalyMinusHalfMatrixSq : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(20 : ℚ), 6, 4, 6;
    8, 12, 16, 0;
    12, 10, 12, 2;
    24, 4, 0, 8]

/-- A generator of the `-1/2` eigenspace. -/
def gaugeAnomalyMinusHalfEigenvector : Fin 4 → ℚ :=
  ![-(1 : ℚ) / 2, 1, -(1 : ℚ) / 2, 1]

/-- A generalized eigenvector whose image is the explicit eigenvector. -/
def gaugeAnomalyMinusHalfGeneralizedVector : Fin 4 → ℚ :=
  ![(1 : ℚ) / 4, -(3 : ℚ) / 2, 1, 0]

/-- The spectral fingerprint of the Parry kernel: the quartic factors as
`(μ - 1)(μ - 1/2)(μ + 1/2)^2`, and the kernel satisfies the matching degree-4 matrix identity. -/
def gaugeAnomalyJordanSpectrumFingerprint : Prop :=
  (∀ μ : ℚ,
      gaugeAnomalyJordanSpectralPolynomial μ =
        (μ - 1) * (μ - 1 / 2) * (μ + 1 / 2) ^ 2) ∧
    gaugeAnomalyJordanParryKernel ^ 4 =
      (1 / 2 : ℚ) • gaugeAnomalyJordanParryKernel ^ 3 +
        (3 / 4 : ℚ) • gaugeAnomalyJordanParryKernel ^ 2 -
          (1 / 8 : ℚ) • gaugeAnomalyJordanParryKernel -
            (1 / 8 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ)

/-- The `-1/2` eigenspace is one-dimensional and the generalized eigenspace is two-dimensional,
realized by an explicit Jordan chain. -/
def gaugeAnomalyJordanBlockAtMinusHalf : Prop :=
  gaugeAnomalyMinusHalfMatrix.mulVec gaugeAnomalyMinusHalfEigenvector = 0 ∧
    gaugeAnomalyMinusHalfMatrix.mulVec gaugeAnomalyMinusHalfGeneralizedVector =
      gaugeAnomalyMinusHalfEigenvector ∧
        (¬ ∃ c : ℚ,
          gaugeAnomalyMinusHalfGeneralizedVector = c • gaugeAnomalyMinusHalfEigenvector) ∧
          (∀ x : Fin 4 → ℚ,
            gaugeAnomalyMinusHalfMatrix.mulVec x = 0 →
              ∃ c : ℚ, x = c • gaugeAnomalyMinusHalfEigenvector) ∧
            (∀ x : Fin 4 → ℚ,
              gaugeAnomalyMinusHalfMatrixSq.mulVec x = 0 →
                ∃ a b : ℚ,
                  x =
                    a • gaugeAnomalyMinusHalfGeneralizedVector +
                      b • gaugeAnomalyMinusHalfEigenvector)

private theorem minusHalfEigenvector_kernel :
    gaugeAnomalyMinusHalfMatrix.mulVec gaugeAnomalyMinusHalfEigenvector = 0 := by
  native_decide

private theorem minusHalfGeneralizedVector_chain :
    gaugeAnomalyMinusHalfMatrix.mulVec gaugeAnomalyMinusHalfGeneralizedVector =
      gaugeAnomalyMinusHalfEigenvector := by
  native_decide

private theorem minusHalfEigenspace_line (x : Fin 4 → ℚ)
    (hx : gaugeAnomalyMinusHalfMatrix.mulVec x = 0) :
    ∃ c : ℚ, x = c • gaugeAnomalyMinusHalfEigenvector := by
  have h0 : 4 * x 0 + x 1 + x 3 = 0 := by
    have := congrFun hx 0
    simpa [gaugeAnomalyMinusHalfMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h1 : 2 * x 1 + 4 * x 2 = 0 := by
    have := congrFun hx 1
    simpa [gaugeAnomalyMinusHalfMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h2 : 2 * x 0 + 2 * x 1 + 2 * x 2 = 0 := by
    have := congrFun hx 2
    simpa [gaugeAnomalyMinusHalfMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h3 : 4 * x 0 + 2 * x 3 = 0 := by
    have := congrFun hx 3
    simpa [gaugeAnomalyMinusHalfMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  refine ⟨x 1, ?_⟩
  ext i
  fin_cases i
  · have hx0 : x 0 = -(x 1) / 2 := by linarith
    simp [gaugeAnomalyMinusHalfEigenvector, hx0]
    ring
  · simp [gaugeAnomalyMinusHalfEigenvector]
  · have hx2 : x 2 = -(x 1) / 2 := by linarith
    simp [gaugeAnomalyMinusHalfEigenvector, hx2]
    ring
  · have hx3 : x 3 = x 1 := by linarith
    simp [gaugeAnomalyMinusHalfEigenvector, hx3]

private theorem minusHalfGeneralizedEigenspace_span (x : Fin 4 → ℚ)
    (hx : gaugeAnomalyMinusHalfMatrixSq.mulVec x = 0) :
    ∃ a b : ℚ,
      x =
        a • gaugeAnomalyMinusHalfGeneralizedVector +
          b • gaugeAnomalyMinusHalfEigenvector := by
  have h0 : 20 * x 0 + 6 * x 1 + 4 * x 2 + 6 * x 3 = 0 := by
    have := congrFun hx 0
    simpa [gaugeAnomalyMinusHalfMatrixSq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h1 : 8 * x 0 + 12 * x 1 + 16 * x 2 = 0 := by
    have := congrFun hx 1
    simpa [gaugeAnomalyMinusHalfMatrixSq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h2 : 12 * x 0 + 10 * x 1 + 12 * x 2 + 2 * x 3 = 0 := by
    have := congrFun hx 2
    simpa [gaugeAnomalyMinusHalfMatrixSq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  have h3 : 24 * x 0 + 4 * x 1 + 8 * x 3 = 0 := by
    have := congrFun hx 3
    simpa [gaugeAnomalyMinusHalfMatrixSq, Matrix.mulVec, dotProduct, Fin.sum_univ_four] using this
  refine ⟨x 2 + x 3 / 2, x 3, ?_⟩
  ext i
  fin_cases i
  · have hx0 : x 0 = x 2 / 4 - 3 * x 3 / 8 := by linarith
    simp [gaugeAnomalyMinusHalfGeneralizedVector, gaugeAnomalyMinusHalfEigenvector, hx0]
    ring
  · have hx1 : x 1 = -(3 * x 2) / 2 + x 3 / 4 := by linarith
    simp [gaugeAnomalyMinusHalfGeneralizedVector, gaugeAnomalyMinusHalfEigenvector, hx1]
    ring
  · simp [gaugeAnomalyMinusHalfGeneralizedVector, gaugeAnomalyMinusHalfEigenvector]
    ring
  · simp [gaugeAnomalyMinusHalfGeneralizedVector, gaugeAnomalyMinusHalfEigenvector]

private theorem minusHalfGeneralizedVector_not_eigenLine :
    ¬ ∃ c : ℚ,
      gaugeAnomalyMinusHalfGeneralizedVector = c • gaugeAnomalyMinusHalfEigenvector := by
  intro h
  rcases h with ⟨c, hc⟩
  have h0 := congrFun hc 3
  have h1 := congrFun hc 0
  simp [gaugeAnomalyMinusHalfGeneralizedVector, gaugeAnomalyMinusHalfEigenvector] at h0 h1
  linarith

private theorem gaugeAnomalyJordanSpectralPolynomial_factor (μ : ℚ) :
    gaugeAnomalyJordanSpectralPolynomial μ =
      (μ - 1) * (μ - 1 / 2) * (μ + 1 / 2) ^ 2 := by
  unfold gaugeAnomalyJordanSpectralPolynomial
  ring

private theorem gaugeAnomalyJordanSpectralMatrixIdentity :
    gaugeAnomalyJordanParryKernel ^ 4 =
      (1 / 2 : ℚ) • gaugeAnomalyJordanParryKernel ^ 3 +
        (3 / 4 : ℚ) • gaugeAnomalyJordanParryKernel ^ 2 -
          (1 / 8 : ℚ) • gaugeAnomalyJordanParryKernel -
            (1 / 8 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by
  native_decide

/-- Paper-facing wrapper exposing the explicit Parry kernel, its row-stochasticity, and the
stationarity of the closed-form distribution `π = (4/9, 2/9, 2/9, 1/9)`. -/
theorem paper_fold_gauge_anomaly_parry_kernel :
    let π : Fin 4 → ℚ := ![(4 / 9 : ℚ), (2 / 9 : ℚ), (2 / 9 : ℚ), (1 / 9 : ℚ)];
    gaugeAnomalyJordanParryKernel =
        !![(1 / 2 : ℚ), (1 / 4 : ℚ), 0, (1 / 4 : ℚ); 0, 0, 1, 0; (1 / 2 : ℚ), (1 / 2 : ℚ), 0, 0;
          1, 0, 0, 0] ∧
      (∀ i, (∑ j, gaugeAnomalyJordanParryKernel i j) = 1) ∧
      (∀ j, (∑ i, π i * gaugeAnomalyJordanParryKernel i j) = π j) := by
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [gaugeAnomalyJordanParryKernel, Fin.sum_univ_four] <;> norm_num
  · intro j
    fin_cases j <;> simp [gaugeAnomalyJordanParryKernel, Fin.sum_univ_four] <;> ring

/-- The gauge-anomaly Parry kernel has the explicit spectral factorization
`(μ - 1)(μ - 1/2)(μ + 1/2)^2`, and `-1/2` carries a size-`2` Jordan block.
    thm:fold-gauge-anomaly-jordan-fingerprint -/
theorem paper_fold_gauge_anomaly_jordan_fingerprint :
    gaugeAnomalyJordanSpectrumFingerprint ∧ gaugeAnomalyJordanBlockAtMinusHalf := by
  refine ⟨?_, ?_⟩
  · exact ⟨gaugeAnomalyJordanSpectralPolynomial_factor, gaugeAnomalyJordanSpectralMatrixIdentity⟩
  · refine ⟨minusHalfEigenvector_kernel, minusHalfGeneralizedVector_chain,
      minusHalfGeneralizedVector_not_eigenLine, minusHalfEigenspace_line,
      minusHalfGeneralizedEigenspace_span⟩

/-- Paper-facing wrapper for the untwisted operator `A₀`: its spectrum has the explicit factorized
fingerprint and `-1/2` supports the unique size-`2` Jordan block.
    thm:fold-gauge-anomaly-A0-jordan -/
theorem paper_fold_gauge_anomaly_a0_jordan :
    gaugeAnomalyJordanSpectrumFingerprint ∧ gaugeAnomalyJordanBlockAtMinusHalf := by
  exact paper_fold_gauge_anomaly_jordan_fingerprint

end Omega.Folding
