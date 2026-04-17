import Mathlib.Tactic

namespace Omega.Zeta

/-- Exponential Nyquist error bounds become proportion bounds after dividing by the positive
spectral energy, and any two sampling depths differ by the sum of their individual relative
errors. -/
theorem paper_zeta_finite_part_nyquist_proportion_stability
    (E_spec K Lambda : ℝ) (hE : 0 < E_spec) (E : ℕ → ℝ)
    (hErr : ∀ q : ℕ, |E q - E_spec| ≤ K * Lambda ^ q) :
    (∀ q : ℕ, |E q / E_spec - 1| ≤ (K / E_spec) * Lambda ^ q) ∧
      ∀ q1 q2 : ℕ,
        |E q1 / E_spec - E q2 / E_spec| ≤ (K / E_spec) * (Lambda ^ q1 + Lambda ^ q2) := by
  have hrel : ∀ q : ℕ, |E q / E_spec - 1| ≤ (K / E_spec) * Lambda ^ q := by
    intro q
    have hrewrite : E q / E_spec - 1 = (E q - E_spec) / E_spec := by
      field_simp [hE.ne']
    rw [hrewrite, abs_div, abs_of_pos hE]
    have hdiv := div_le_div_of_nonneg_right (hErr q) (le_of_lt hE)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  refine ⟨hrel, ?_⟩
  · intro q1 q2
    have hq1 : |E q1 / E_spec - 1| ≤ (K / E_spec) * Lambda ^ q1 := hrel q1
    have hq2 : |E q2 / E_spec - 1| ≤ (K / E_spec) * Lambda ^ q2 := hrel q2
    calc
      |E q1 / E_spec - E q2 / E_spec|
          ≤ |E q1 / E_spec - 1| + |1 - E q2 / E_spec| := by
            exact abs_sub_le (E q1 / E_spec) 1 (E q2 / E_spec)
      _ = |E q1 / E_spec - 1| + |E q2 / E_spec - 1| := by
            congr 1
            exact abs_sub_comm 1 (E q2 / E_spec)
      _ ≤ (K / E_spec) * Lambda ^ q1 + (K / E_spec) * Lambda ^ q2 := add_le_add hq1 hq2
      _ = (K / E_spec) * (Lambda ^ q1 + Lambda ^ q2) := by ring
