import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.Zeta.HankelVandermondeFiniteBlaschke

namespace Omega.Zeta

/-- Concrete numerical package for the lower bound on the smallest Hankel singular value coming
from a determinant lower bound and the operator/Hilbert--Schmidt norm estimate. -/
structure XiHankelSigminLowerboundData where
  k : ℕ
  M : ℝ
  detH : ℝ
  sigmaMax : ℝ
  sigmaMin : ℝ
  vandermondeLower : ℝ
  hM_nonneg : 0 ≤ M
  hsigmaMax_nonneg : 0 ≤ sigmaMax
  hsigmaMin_nonneg : 0 ≤ sigmaMin
  determinant_vs_singular :
    |detH| ≤ sigmaMax ^ (k - 1) * sigmaMin
  operator_norm_vs_mass :
    sigmaMax ≤ (k : ℝ) * M
  vandermonde_bound :
    vandermondeLower ≤ |detH|

namespace XiHankelSigminLowerboundData

/-- The determinant is bounded below by the Vandermonde-separation package. -/
def determinantLowerBound (D : XiHankelSigminLowerboundData) : Prop :=
  D.vandermondeLower ≤ |D.detH|

/-- The operator norm is bounded above by the Hilbert--Schmidt estimate `k M`. -/
def operatorNormUpperBound (D : XiHankelSigminLowerboundData) : Prop :=
  D.sigmaMax ≤ (D.k : ℝ) * D.M

/-- Combining the determinant estimate with the operator/Hilbert--Schmidt bound yields the
advertised lower-bound package for `σ_min`. -/
def sigmaMinLowerBound (D : XiHankelSigminLowerboundData) : Prop :=
  D.vandermondeLower ≤ ((D.k : ℝ) * D.M) ^ (D.k - 1) * D.sigmaMin

end XiHankelSigminLowerboundData

/-- Paper label: `cor:xi-hankel-sigmin-lowerbound-vandermonde-separation`.
The Vandermonde determinant lower bound is chained with the singular-value determinant estimate
and the `‖H‖_op ≤ ‖H‖_HS ≤ k M` bound to package the resulting `σ_min` inequality. -/
theorem paper_xi_hankel_sigmin_lowerbound_vandermonde_separation
    (D : XiHankelSigminLowerboundData) :
    D.determinantLowerBound ∧ D.operatorNormUpperBound ∧ D.sigmaMinLowerBound := by
  have hpow :
      D.sigmaMax ^ (D.k - 1) ≤ (((D.k : ℝ) * D.M) ^ (D.k - 1)) := by
    exact pow_le_pow_left₀ D.hsigmaMax_nonneg D.operator_norm_vs_mass (D.k - 1)
  refine ⟨D.vandermonde_bound, D.operator_norm_vs_mass, ?_⟩
  calc
    D.vandermondeLower ≤ |D.detH| := D.vandermonde_bound
    _ ≤ D.sigmaMax ^ (D.k - 1) * D.sigmaMin := D.determinant_vs_singular
    _ ≤ ((D.k : ℝ) * D.M) ^ (D.k - 1) * D.sigmaMin := by
          exact mul_le_mul_of_nonneg_right hpow D.hsigmaMin_nonneg

end Omega.Zeta
