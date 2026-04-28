import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-defect-entropy-forces-negative-block-mass`. -/
theorem paper_xi_defect_entropy_forces_negative_block_mass (κ : ℕ)
    (opNorm frobSq u0 Sdef : ℝ) (hκ : 0 < κ) (havg : frobSq / (κ : ℝ) ≤ opNorm)
    (hentry : u0 ^ 2 ≤ frobSq) (hu0 : u0 = 4 * Real.pi * Sdef) :
    u0 ^ 2 / (κ : ℝ) ≤ opNorm ∧
      (4 * Real.pi * Sdef) ^ 2 / (κ : ℝ) ≤ opNorm := by
  have hκ_pos : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have hκ_nonneg : 0 ≤ (κ : ℝ) := le_of_lt hκ_pos
  have hdiv : u0 ^ 2 / (κ : ℝ) ≤ frobSq / (κ : ℝ) :=
    div_le_div_of_nonneg_right hentry hκ_nonneg
  have hmain : u0 ^ 2 / (κ : ℝ) ≤ opNorm := hdiv.trans havg
  exact ⟨hmain, by simpa [hu0] using hmain⟩

end Omega.Zeta
