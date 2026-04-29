import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-escort-all-renyi-rate-freezing`. -/
theorem paper_conclusion_binfold_escort_all_renyi_rate_freezing
    (H : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbounded :
      ∀ m, 0 < m →
        |H m - (m : ℝ) * Real.log Real.goldenRatio| ≤ C)
    (hsmall :
      ∀ ε, 0 < ε →
        ∃ N, ∀ m, N ≤ m → 0 < m → C / (m : ℝ) ≤ ε) :
    ∀ ε, 0 < ε →
      ∃ N, ∀ m, N ≤ m → 0 < m →
        |H m / (m : ℝ) - Real.log Real.goldenRatio| ≤ ε := by
  intro ε hε
  rcases hsmall ε hε with ⟨N₀, hN₀⟩
  rcases exists_nat_ge N₀ with ⟨N, hN₀_le_N⟩
  refine ⟨N, ?_⟩
  intro m hmN hmpos
  have hN₀_le_m : N₀ ≤ (m : ℝ) := by
    exact hN₀_le_N.trans (by exact_mod_cast hmN)
  have hmposℝ : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hbound := hbounded m hmpos
  have hrearrange :
      H m / (m : ℝ) - Real.log Real.goldenRatio =
        (H m - (m : ℝ) * Real.log Real.goldenRatio) / (m : ℝ) := by
    field_simp [hmposℝ.ne']
  calc
    |H m / (m : ℝ) - Real.log Real.goldenRatio|
        = |(H m - (m : ℝ) * Real.log Real.goldenRatio) / (m : ℝ)| := by
          rw [hrearrange]
    _ = |H m - (m : ℝ) * Real.log Real.goldenRatio| / (m : ℝ) := by
          rw [abs_div, abs_of_pos hmposℝ]
    _ ≤ C / (m : ℝ) := by
          exact div_le_div_of_nonneg_right hbound (le_of_lt hmposℝ)
    _ ≤ ε := by
          have : 0 ≤ C / (m : ℝ) := div_nonneg hC (le_of_lt hmposℝ)
          exact hN₀ m hN₀_le_m hmposℝ

end Omega.Conclusion
