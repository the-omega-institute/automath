import Mathlib.Tactic
import Omega.Zeta.ToeplitzNegativeInertiaAllowedPerturbRadius

namespace Omega.Zeta

/-- Concrete perturbative data for the negative-subspace threshold corollary. The values
`witnessQuadraticForm i` model the quadratic form of the perturbed Toeplitz truncation on the
`kappa` distinguished directions `R_N (0 ⊕ v_i)`, and `witnessBound` is the exact operator-norm
estimate coming from the negative Hankel block lower bound `sigmaMinH ^ 2`. -/
structure ToeplitzNegativeSubspacePreservationThresholdData where
  kappa : ℕ
  opNormEN : ℝ
  sigmaMinH : ℝ
  opNormR : ℝ
  witnessQuadraticForm : Fin kappa → ℝ
  opNormR_pos : 0 < opNormR
  witnessBound :
    ∀ i, witnessQuadraticForm i ≤ opNormR ^ 2 * opNormEN - sigmaMinH ^ 2

namespace ToeplitzNegativeSubspacePreservationThresholdData

/-- The `kappa` distinguished directions remain strictly negative after perturbation. -/
def negativeInertiaLowerBound (D : ToeplitzNegativeSubspacePreservationThresholdData) : Prop :=
  ∀ i, D.witnessQuadraticForm i < 0

end ToeplitzNegativeSubspacePreservationThresholdData

open ToeplitzNegativeSubspacePreservationThresholdData

/-- If the perturbation is smaller than the explicit Hankel-block threshold
`sigmaMinH ^ 2 / ‖R_N‖^2`, then the `kappa`-dimensional negative subspace survives.
    cor:xi-toeplitz-negative-subspace-preservation-threshold -/
theorem paper_xi_toeplitz_negative_subspace_preservation_threshold
    (D : ToeplitzNegativeSubspacePreservationThresholdData) :
    D.opNormEN < D.sigmaMinH ^ 2 / D.opNormR ^ 2 → D.negativeInertiaLowerBound := by
  intro hThreshold
  have hR2pos : 0 < D.opNormR ^ 2 := sq_pos_of_pos D.opNormR_pos
  have hScaled : D.opNormR ^ 2 * D.opNormEN < D.sigmaMinH ^ 2 := by
    have hScaled' : D.opNormEN * D.opNormR ^ 2 < D.sigmaMinH ^ 2 :=
      (_root_.lt_div_iff₀ hR2pos).mp hThreshold
    simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled'
  intro i
  have hBound := D.witnessBound i
  have hNeg : D.opNormR ^ 2 * D.opNormEN - D.sigmaMinH ^ 2 < 0 := by
    linarith
  exact lt_of_le_of_lt hBound hNeg

end Omega.Zeta
