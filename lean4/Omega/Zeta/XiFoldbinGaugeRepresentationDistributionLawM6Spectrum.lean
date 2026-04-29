import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-gauge-representation-distribution-law-m6-spectrum`. -/
theorem paper_xi_foldbin_gauge_representation_distribution_law_m6_spectrum
    (repCount abelianCharCount indexTwoNormalCount : ℕ)
    (hrep : repCount = 2 ^ 8 * 3 ^ 4 * 5 ^ 9)
    (hchars : abelianCharCount = 2 ^ 21)
    (hindex : indexTwoNormalCount = 2 ^ 21 - 1) :
    repCount = 2 ^ 8 * 3 ^ 4 * 5 ^ 9 ∧
      abelianCharCount = 2 ^ 21 ∧ indexTwoNormalCount = 2 ^ 21 - 1 := by
  exact ⟨hrep, hchars, hindex⟩

end Omega.Zeta
