import Mathlib.Tactic
import Omega.Zeta.XiBinomialToeplitzDominantPoleResponse

namespace Omega.Zeta

noncomputable section

/-- Negative-endpoint growth rate `A = |w - 1|² / |w|` written in `(r, x)` coordinates with
`r = |w|` and `x = Re(w)`. -/
def xi_binomial_toeplitz_two_endpoint_pole_inversion_negativeGrowth (r x : ℝ) : ℝ :=
  (r ^ (2 : Nat) - 2 * x + 1) / r

/-- Positive-endpoint growth rate `B = |w + 1|² / |w|` written in `(r, x)` coordinates with
`r = |w|` and `x = Re(w)`. -/
def xi_binomial_toeplitz_two_endpoint_pole_inversion_positiveGrowth (r x : ℝ) : ℝ :=
  (r ^ (2 : Nat) + 2 * x + 1) / r

/-- The quadratic whose unique root in `(0, 1)` recovers the dominant-pole modulus. -/
def xi_binomial_toeplitz_two_endpoint_pole_inversion_radiusPolynomial
    (A B r : ℝ) : ℝ :=
  2 * r ^ (2 : Nat) - (A + B) * r + 2

/-- Paper label: `thm:xi-binomial-toeplitz-two-endpoint-pole-inversion`.
Applying the dominant-pole response package to both endpoint witnesses produces the two closed
response laws; from the paired growth rates one recovers the quadratic for the radius and the
real part `x` from `A - B`. -/
theorem paper_xi_binomial_toeplitz_two_endpoint_pole_inversion
    (Dneg Dpos : XiBinomialToeplitzDominantPoleResponseData) (r x : ℝ) (hr : 0 < r)
    (hneg :
      Dneg.dominantPole =
        xi_binomial_toeplitz_two_endpoint_pole_inversion_negativeGrowth r x)
    (hpos :
      Dpos.dominantPole =
        xi_binomial_toeplitz_two_endpoint_pole_inversion_positiveGrowth r x) :
    Dneg.closedFormResponseLaw ∧ Dneg.remainderBoundLaw ∧
      Dpos.closedFormResponseLaw ∧ Dpos.remainderBoundLaw ∧
      xi_binomial_toeplitz_two_endpoint_pole_inversion_radiusPolynomial
          Dneg.dominantPole Dpos.dominantPole r = 0 ∧
      x = -((Dneg.dominantPole - Dpos.dominantPole) * r) / 4 := by
  have hneg_pkg := paper_xi_binomial_toeplitz_dominant_pole_response Dneg
  have hpos_pkg := paper_xi_binomial_toeplitz_dominant_pole_response Dpos
  refine ⟨hneg_pkg.1, hneg_pkg.2, hpos_pkg.1, hpos_pkg.2, ?_, ?_⟩
  · unfold xi_binomial_toeplitz_two_endpoint_pole_inversion_radiusPolynomial
    rw [hneg, hpos]
    unfold xi_binomial_toeplitz_two_endpoint_pole_inversion_negativeGrowth
      xi_binomial_toeplitz_two_endpoint_pole_inversion_positiveGrowth
    field_simp [hr.ne']
    nlinarith
  · rw [hneg, hpos]
    unfold xi_binomial_toeplitz_two_endpoint_pole_inversion_negativeGrowth
      xi_binomial_toeplitz_two_endpoint_pole_inversion_positiveGrowth
    field_simp [hr.ne']
    nlinarith

end

end Omega.Zeta
