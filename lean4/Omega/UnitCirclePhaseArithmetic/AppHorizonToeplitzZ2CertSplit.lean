import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.AppHorizonToeplitzZ2Splitting

namespace Omega.UnitCirclePhaseArithmetic

/-- Paper label: `cor:app-horizon-toeplitz-z2-cert-split`. In the concrete `2 × 2`
reversal-symmetric Toeplitz model, PSD is equivalent to simultaneous positivity of the even and
odd blocks. Therefore a PSD failure is exactly a sector-local obstruction in one of the two
`\ZZ/2` blocks. -/
theorem paper_app_horizon_toeplitz_z2_cert_split (diag off : ℝ) :
    let D : app_horizon_toeplitz_z2_splitting_data := ⟨diag, off⟩
    (D.toeplitz_psd ↔ D.even_block_psd ∧ D.odd_block_psd) ∧
      (¬ D.toeplitz_psd ↔ ¬ D.even_block_psd ∨ ¬ D.odd_block_psd) := by
  let D : app_horizon_toeplitz_z2_splitting_data := ⟨diag, off⟩
  change (D.toeplitz_psd ↔ D.even_block_psd ∧ D.odd_block_psd) ∧
      (¬ D.toeplitz_psd ↔ ¬ D.even_block_psd ∨ ¬ D.odd_block_psd)
  have hsplit : D.toeplitz_psd ↔ D.even_block_psd ∧ D.odd_block_psd := by
    exact (paper_app_horizon_toeplitz_z2_splitting D).2.2
  refine ⟨hsplit, ?_⟩
  constructor
  · intro hnot
    by_cases he : D.even_block_psd
    · right
      intro ho
      exact hnot (hsplit.mpr ⟨he, ho⟩)
    · exact Or.inl he
  · rintro (he | ho) hpsd
    · exact he (hsplit.mp hpsd).1
    · exact ho (hsplit.mp hpsd).2

end Omega.UnitCirclePhaseArithmetic
