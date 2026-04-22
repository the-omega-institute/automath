import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete data package for the odd Bernoulli-germ coefficients and the lower-growth estimate
used in the root-test argument. -/
structure conclusion_foldgauge_pi_zero_radius_odd_germ_data where
  conclusion_foldgauge_pi_zero_radius_odd_germ_start : ℕ
  conclusion_foldgauge_pi_zero_radius_odd_germ_start_pos :
    1 ≤ conclusion_foldgauge_pi_zero_radius_odd_germ_start
  conclusion_foldgauge_pi_zero_radius_odd_germ_coeff : ℕ → ℝ
  conclusion_foldgauge_pi_zero_radius_odd_germ_formula :
    ∀ r, 1 ≤ r →
      conclusion_foldgauge_pi_zero_radius_odd_germ_coeff r =
        (((bernoulli (2 * r) : ℚ) : ℝ) / ((r : ℝ) * (2 * r - 1))) *
          (Real.goldenRatio⁻¹ + Real.goldenRatio ^ (2 * r) / Real.goldenRatio ^ 3)
  conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant : ℝ
  conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant_pos :
    0 <
      conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant
  conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth :
    ∀ r,
      conclusion_foldgauge_pi_zero_radius_odd_germ_start ≤ r →
        conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant * r ≤
          |conclusion_foldgauge_pi_zero_radius_odd_germ_coeff r| ^ (1 / (2 * r - 1 : ℝ))

namespace conclusion_foldgauge_pi_zero_radius_odd_germ_data

/-- The odd-root profile governing the Cauchy-Hadamard radius computation. -/
def conclusion_foldgauge_pi_zero_radius_odd_germ_root_profile
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) (r : ℕ) : ℝ :=
  |D.conclusion_foldgauge_pi_zero_radius_odd_germ_coeff r| ^ (1 / (2 * r - 1 : ℝ))

/-- A concrete zero-radius formulation: the odd root profile eventually exceeds every positive
threshold. -/
def conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) : Prop :=
  ∀ K : ℝ,
    0 < K →
      ∃ r ≥ D.conclusion_foldgauge_pi_zero_radius_odd_germ_start,
        K ≤ D.conclusion_foldgauge_pi_zero_radius_odd_germ_root_profile r

end conclusion_foldgauge_pi_zero_radius_odd_germ_data

open conclusion_foldgauge_pi_zero_radius_odd_germ_data

/-- A linear lower bound on the odd root profile forces the formal odd germ to have radius zero in
the Cauchy-Hadamard sense encoded by `conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius`. -/
lemma conclusion_foldgauge_pi_zero_radius_odd_germ_root_test_lemma
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) :
    D.conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius := by
  intro K hK
  let n : ℕ :=
    Nat.ceil (K / D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant)
  let r : ℕ := max D.conclusion_foldgauge_pi_zero_radius_odd_germ_start n
  have hr_start : D.conclusion_foldgauge_pi_zero_radius_odd_germ_start ≤ r := le_max_left _ _
  have hceil :
      K / D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant ≤ n :=
    Nat.le_ceil _
  have hn_le : (n : ℝ) ≤ r := by
    exact_mod_cast (le_max_right D.conclusion_foldgauge_pi_zero_radius_odd_germ_start n)
  have hlower :
      K ≤ D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant * r := by
    have hKn :
        K ≤ D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant * n := by
      have := (div_le_iff₀
        D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant_pos).mp hceil
      simpa [mul_comm] using this
    nlinarith [hKn, hn_le, D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth_constant_pos]
  refine ⟨r, hr_start, ?_⟩
  exact le_trans hlower (D.conclusion_foldgauge_pi_zero_radius_odd_germ_lower_growth r hr_start)

/-- Paper label: `thm:conclusion-foldgauge-pi-zero-radius-odd-germ`. -/
theorem paper_conclusion_foldgauge_pi_zero_radius_odd_germ
    (D : conclusion_foldgauge_pi_zero_radius_odd_germ_data) :
    D.conclusion_foldgauge_pi_zero_radius_odd_germ_zero_radius := by
  exact conclusion_foldgauge_pi_zero_radius_odd_germ_root_test_lemma D

end

end Omega.Conclusion
