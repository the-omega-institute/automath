import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `prop:xi-scan-toeplitz-conditioning-by-separation`. -/
theorem paper_xi_scan_toeplitz_conditioning_by_separation
    (lambdaMin sep pMax rhoMin rMax lower : ℝ) (κ : ℕ)
    (hLower : lower ≤ lambdaMin)
    (hUpper : lambdaMin ≤ pMax * rhoMin ^ 2)
    (hRho : rhoMin ≤ sep / (1 - rMax ^ 2))
    (hpMax : 0 ≤ pMax)
    (hrho : 0 ≤ rhoMin)
    (hSepRatio : 0 ≤ sep / (1 - rMax ^ 2)) :
    lower ≤ lambdaMin ∧ lambdaMin ≤ pMax * (sep / (1 - rMax ^ 2)) ^ 2 := by
  have _ := κ
  have hsq : rhoMin ^ 2 ≤ (sep / (1 - rMax ^ 2)) ^ 2 := by
    exact (sq_le_sq₀ hrho hSepRatio).2 hRho
  exact ⟨hLower, hUpper.trans (mul_le_mul_of_nonneg_left hsq hpMax)⟩

end Omega.Zeta
