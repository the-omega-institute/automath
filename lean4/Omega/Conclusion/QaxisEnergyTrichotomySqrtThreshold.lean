import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-qaxis-energy-trichotomy-sqrt-threshold`.

Concrete square-root threshold algebra for the `q`-axis energy trichotomy.  For a positive
Perron scale `rho` and nonnegative exterior spectral radius `Lambda`, comparing `Lambda` with
`rho^{-1/2}` is equivalent to comparing the energy ratio `rho * Lambda^2` with `1`; these are the
three regimes used by the Cesaro energy argument. -/
theorem paper_conclusion_qaxis_energy_trichotomy_sqrt_threshold
    (rho Lambda : ℝ) (hrho : 0 < rho) (hLambda : 0 ≤ Lambda) :
    (Lambda < 1 / Real.sqrt rho ∧ rho * Lambda ^ 2 < 1) ∨
      (Lambda = 1 / Real.sqrt rho ∧ rho * Lambda ^ 2 = 1) ∨
      (1 / Real.sqrt rho < Lambda ∧ 1 < rho * Lambda ^ 2) := by
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hthreshold_pos : 0 < 1 / Real.sqrt rho := one_div_pos.mpr hsqrt_pos
  have hthreshold_sq : (1 / Real.sqrt rho) ^ 2 = 1 / rho := by
    rw [one_div_pow, Real.sq_sqrt (le_of_lt hrho)]
  have hrho_mul_inv : rho * (1 / rho) = 1 := by
    field_simp [ne_of_gt hrho]
  rcases lt_trichotomy Lambda (1 / Real.sqrt rho) with hlt | heq | hgt
  · left
    have hsq_lt : Lambda ^ 2 < (1 / Real.sqrt rho) ^ 2 := by
      nlinarith [hLambda, hthreshold_pos, hlt]
    have hscaled : rho * Lambda ^ 2 < rho * ((1 / Real.sqrt rho) ^ 2) :=
      mul_lt_mul_of_pos_left hsq_lt hrho
    constructor
    · exact hlt
    · nlinarith [hthreshold_sq, hrho_mul_inv, hscaled]
  · right
    left
    constructor
    · exact heq
    · subst Lambda
      nlinarith [hthreshold_sq, hrho_mul_inv]
  · right
    right
    have hLambda_pos : 0 < Lambda := lt_trans hthreshold_pos hgt
    have hsq_lt : (1 / Real.sqrt rho) ^ 2 < Lambda ^ 2 := by
      nlinarith [hthreshold_pos, hLambda_pos, hgt]
    have hscaled : rho * ((1 / Real.sqrt rho) ^ 2) < rho * Lambda ^ 2 :=
      mul_lt_mul_of_pos_left hsq_lt hrho
    constructor
    · exact hgt
    · nlinarith [hthreshold_sq, hrho_mul_inv, hscaled]

end Omega.Conclusion
