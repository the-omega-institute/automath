import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic
import Omega.Conclusion.ShiftCommutingAlgorithmsPolynomial

namespace Omega.Conclusion

open Polynomial

/-- Prime-register mass scaling in the scalar shift-commuting model is measured at `z = 1`. -/
def conclusion_polynomial_algorithm_spectral_radius_mass_mass (f : Polynomial ℕ) : ℕ :=
  f.eval 1

/-- Spectral-radius side of the same scalar model, maximized at `z = 1` for nonnegative
coefficients. -/
def conclusion_polynomial_algorithm_spectral_radius_mass_spectral_radius (f : Polynomial ℕ) : ℕ :=
  f.eval 1

/-- Concrete prime-register mass obtained by summing the nonnegative coefficients. -/
def conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum (f : Polynomial ℕ) : ℕ :=
  Finset.sum f.support fun n => f.coeff n

/-- Paper-facing package for the polynomial mass/radius comparison. -/
abbrev ConclusionPolynomialAlgorithmSpectralRadiusMass (f : Polynomial ℕ) : Prop :=
  conclusion_polynomial_algorithm_spectral_radius_mass_mass f =
      conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum f ∧
    conclusion_polynomial_algorithm_spectral_radius_mass_spectral_radius f =
      conclusion_polynomial_algorithm_spectral_radius_mass_mass f ∧
    0 < conclusion_polynomial_algorithm_spectral_radius_mass_mass f

lemma conclusion_polynomial_algorithm_spectral_radius_mass_eval_one_eq_mass_sum
    (f : Polynomial ℕ) :
    conclusion_polynomial_algorithm_spectral_radius_mass_mass f =
      conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum f := by
  rw [conclusion_polynomial_algorithm_spectral_radius_mass_mass,
    conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum, Polynomial.eval_eq_sum,
    Polynomial.sum_def]
  simp

lemma conclusion_polynomial_algorithm_spectral_radius_mass_positive (f : Polynomial ℕ)
    (hf : f ≠ 0) : 0 < conclusion_polynomial_algorithm_spectral_radius_mass_mass f := by
  rw [conclusion_polynomial_algorithm_spectral_radius_mass_eval_one_eq_mass_sum]
  have hs : f.support.Nonempty := by
    simpa using (Polynomial.support_nonempty.mpr hf)
  rcases hs with ⟨n, hn⟩
  have hcoeff : 0 < f.coeff n := by
    exact Nat.pos_of_ne_zero (by simpa [Polynomial.mem_support_iff] using hn)
  have hsingle :
      f.coeff n ≤ conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum f := by
    exact Finset.single_le_sum (fun m hm => Nat.zero_le _) (by simpa
      [conclusion_polynomial_algorithm_spectral_radius_mass_mass_sum] using hn)
  exact lt_of_lt_of_le hcoeff hsingle

/-- Paper label: `prop:conclusion-polynomial-algorithm-spectral-radius-mass`. In the concrete
shift-commuting polynomial model, the prime-register mass scaling and the spectral-radius bound
are both given by evaluation at `1`, and a nonzero polynomial over `ℕ` has strictly positive mass
there. -/
theorem paper_conclusion_polynomial_algorithm_spectral_radius_mass (f : Polynomial ℕ)
    (hf : f ≠ 0) : ConclusionPolynomialAlgorithmSpectralRadiusMass f := by
  refine ⟨conclusion_polynomial_algorithm_spectral_radius_mass_eval_one_eq_mass_sum f, rfl, ?_⟩
  exact conclusion_polynomial_algorithm_spectral_radius_mass_positive f hf

end Omega.Conclusion
