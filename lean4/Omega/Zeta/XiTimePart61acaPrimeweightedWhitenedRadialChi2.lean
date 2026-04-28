import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

/-- The radial square in whitened two-dimensional coordinates. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquare
    (x : Fin 2 → ℝ) : ℝ :=
  x 0 ^ 2 + x 1 ^ 2

/-- The CDF of a chi-square random variable with two degrees of freedom. -/
noncomputable def xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf
    (t : ℝ) : ℝ :=
  if 0 ≤ t then 1 - Real.exp (-(t / 2)) else 0

/-- Concrete data for the prime-weighted elliptic fingerprint after a linear whitening map. -/
structure xi_time_part61aca_primeweighted_whitened_radial_chi2_data where
  rawFingerprint : ℕ → Fin 2 → ℝ
  whitenedFingerprint : ℕ → Fin 2 → ℝ
  whiteningMap : (Fin 2 → ℝ) → Fin 2 → ℝ
  radialSquareLimitCdf : ℝ → ℝ
  whiteningMap_spec :
    ∀ n, whitenedFingerprint n = whiteningMap (rawFingerprint n)
  standardGaussianRadialSquareLimit :
    ∀ t,
      radialSquareLimitCdf t =
        xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf t

namespace xi_time_part61aca_primeweighted_whitened_radial_chi2_data

/-- Radial square process after applying the supplied whitening map. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquareProcess
    (D : xi_time_part61aca_primeweighted_whitened_radial_chi2_data) (n : ℕ) : ℝ :=
  xi_time_part61aca_primeweighted_whitened_radial_chi2_radialSquare (D.whitenedFingerprint n)

/-- Paper-facing clauses: whitening is applied to the fingerprint, the radial-square limit is
chi-square with two degrees of freedom, and the CDF has its explicit positive/negative branches. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_clauses
    (D : xi_time_part61aca_primeweighted_whitened_radial_chi2_data) : Prop :=
  (∀ n, D.whitenedFingerprint n = D.whiteningMap (D.rawFingerprint n)) ∧
    (∀ t,
      D.radialSquareLimitCdf t =
        xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf t) ∧
    (∀ t, 0 ≤ t → D.radialSquareLimitCdf t = 1 - Real.exp (-(t / 2))) ∧
      ∀ t, t < 0 → D.radialSquareLimitCdf t = 0

end xi_time_part61aca_primeweighted_whitened_radial_chi2_data

/-- Root-level paper statement name used by the target theorem. -/
def xi_time_part61aca_primeweighted_whitened_radial_chi2_statement
    (D : xi_time_part61aca_primeweighted_whitened_radial_chi2_data) : Prop :=
  D.xi_time_part61aca_primeweighted_whitened_radial_chi2_clauses

/-- Paper label: `thm:xi-time-part61aca-primeweighted-whitened-radial-chi2`. -/
theorem paper_xi_time_part61aca_primeweighted_whitened_radial_chi2
    (D : xi_time_part61aca_primeweighted_whitened_radial_chi2_data) :
    xi_time_part61aca_primeweighted_whitened_radial_chi2_statement D := by
  refine ⟨D.whiteningMap_spec, D.standardGaussianRadialSquareLimit, ?_, ?_⟩
  · intro t ht
    rw [D.standardGaussianRadialSquareLimit]
    simp [xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf, ht]
  · intro t ht
    rw [D.standardGaussianRadialSquareLimit]
    have hnot : ¬ 0 ≤ t := not_le_of_gt ht
    simp [xi_time_part61aca_primeweighted_whitened_radial_chi2_chi2TwoCdf, hnot]

end Omega.Zeta
