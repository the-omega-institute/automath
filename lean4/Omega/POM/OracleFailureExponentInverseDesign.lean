import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-oracle-failure-exponent-inverse-design`. -/
theorem paper_pom_oracle_failure_exponent_inverse_design
    (G E : ℝ → ℝ) (logTwo e c_e alpha_e : ℝ) (hlog : 0 < logTwo)
    (hE : ∀ α, E α = logTwo - G (α * logTwo)) (halpha : alpha_e * logTwo = c_e)
    (hthreshold : ∀ c, G c ≤ logTwo - e ↔ c_e ≤ c) :
    ∀ α, E α ≥ e ↔ alpha_e ≤ α := by
  intro α
  constructor
  · intro hEge
    have hG : G (α * logTwo) ≤ logTwo - e := by
      rw [hE α] at hEge
      linarith
    have hc : c_e ≤ α * logTwo := (hthreshold (α * logTwo)).mp hG
    have hmul : alpha_e * logTwo ≤ α * logTwo := by
      simpa [halpha] using hc
    nlinarith
  · intro halpha_le
    have hmul : alpha_e * logTwo ≤ α * logTwo := by
      nlinarith
    have hc : c_e ≤ α * logTwo := by
      simpa [halpha] using hmul
    have hG : G (α * logTwo) ≤ logTwo - e := (hthreshold (α * logTwo)).mpr hc
    rw [hE α]
    linarith

end Omega.POM
