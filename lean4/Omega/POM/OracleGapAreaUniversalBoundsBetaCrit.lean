import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-oracle-gap-area-universal-bounds-beta-crit`. -/
theorem paper_pom_oracle_gap_area_universal_bounds_beta_crit
    (A_gap delta logTwo logPhi a1 betaCrit : ℝ) (hlogTwo_pos : 0 < logTwo)
    (hdelta : delta = logTwo - logPhi) (harea_lower : delta ^ 2 ≤ 2 * A_gap)
    (harea_upper : 2 * A_gap ≤ logTwo * delta) (ha1 : delta ≤ a1)
    (hbeta : betaCrit = a1 / logTwo) :
    delta ^ 2 / 2 ≤ A_gap ∧ A_gap ≤ logTwo * delta / 2 ∧ delta ≤ a1 ∧
      1 - logPhi / logTwo ≤ betaCrit := by
  have hgap_lower : delta ^ 2 / 2 ≤ A_gap := by
    nlinarith
  have hgap_upper : A_gap ≤ logTwo * delta / 2 := by
    nlinarith
  have hdelta_div_le : delta / logTwo ≤ a1 / logTwo := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right ha1 (by positivity)
  have hdelta_div :
      delta / logTwo = 1 - logPhi / logTwo := by
    rw [hdelta]
    field_simp [hlogTwo_pos.ne']
  exact ⟨hgap_lower, hgap_upper, ha1, by simpa [hbeta, hdelta_div] using hdelta_div_le⟩

end Omega.POM
