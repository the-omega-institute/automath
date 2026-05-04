import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-xi-small-remainder-linearized-sigma-bound`.

This scalar wrapper takes the posterior real-part compression estimate and the small-remainder
linearization of `log ((1 + eta) / (1 - eta))` as hypotheses, then substitutes the latter into
the former. -/
theorem paper_conclusion_xi_small_remainder_linearized_sigma_bound
    (sigma eta eta0 q logScale deltaChi taylorRemainder : ℝ)
    (heta_pos : 0 < eta) (heta_le_eta0 : eta ≤ eta0) (heta0_lt_one : eta0 < 1)
    (hposterior :
      |sigma - (1 / 2 : ℝ)| ≤
        (Real.log ((1 + eta) / (1 - eta)) + |deltaChi|) / ((1 - q) * logScale))
    (htaylor :
      Real.log ((1 + eta) / (1 - eta)) ≤ 2 * eta + taylorRemainder)
    (hden_pos : 0 < (1 - q) * logScale) :
    |sigma - (1 / 2 : ℝ)| ≤
      (2 * eta + taylorRemainder + |deltaChi|) / ((1 - q) * logScale) := by
  have _ : 0 < eta := heta_pos
  have _ : eta < 1 := lt_of_le_of_lt heta_le_eta0 heta0_lt_one
  have hnum :
      Real.log ((1 + eta) / (1 - eta)) + |deltaChi| ≤
        2 * eta + taylorRemainder + |deltaChi| := by
    linarith
  have hdiv :
      (Real.log ((1 + eta) / (1 - eta)) + |deltaChi|) / ((1 - q) * logScale) ≤
        (2 * eta + taylorRemainder + |deltaChi|) / ((1 - q) * logScale) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
  exact le_trans hposterior hdiv

end Omega.Conclusion
