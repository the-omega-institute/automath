import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-dirichlet-even-modulus-uniform-parity-obstruction`. -/
theorem paper_conclusion_dirichlet_even_modulus_uniform_parity_obstruction
    (m : ℕ) (theta_m beta_par : ℝ) (hm_ge : 2 ≤ m) (hm_even : ∃ j, m = 2 * j)
    (hpar : beta_par ≤ theta_m) (hgt : (1 : ℝ) / 2 < beta_par) :
    ∃ j, 1 ≤ j ∧ j < m ∧ m = 2 * j ∧ (1 : ℝ) / 2 < theta_m := by
  rcases hm_even with ⟨j, rfl⟩
  have hj_pos : 1 ≤ j := by omega
  have hj_lt : j < 2 * j := by omega
  have htheta_gt : (1 : ℝ) / 2 < theta_m := lt_of_lt_of_le hgt hpar
  exact ⟨j, hj_pos, hj_lt, rfl, htheta_gt⟩

end Omega.Conclusion
