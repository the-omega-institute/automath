import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete normalized two-spectrum data for the Lee--Yang logarithmic shift estimate.  The
zero equation records the two dominant modes after division by the leading spectrum; the
remainder and envelope fields record the exponentially small discarded spectrum. -/
structure xi_leyang_logshift_two_spectrum_data where
  xi_leyang_logshift_two_spectrum_center : ℝ
  xi_leyang_logshift_two_spectrum_zero : ℕ → ℝ
  xi_leyang_logshift_two_spectrum_remainder : ℕ → ℝ
  xi_leyang_logshift_two_spectrum_envelope : ℕ → ℝ
  xi_leyang_logshift_two_spectrum_prefactor : ℝ
  xi_leyang_logshift_two_spectrum_theta : ℝ
  xi_leyang_logshift_two_spectrum_zero_equation :
    ∀ n,
      (xi_leyang_logshift_two_spectrum_zero n -
          xi_leyang_logshift_two_spectrum_center) +
        xi_leyang_logshift_two_spectrum_remainder n =
          0
  xi_leyang_logshift_two_spectrum_remainder_bound :
    ∀ n,
      |xi_leyang_logshift_two_spectrum_remainder n| ≤
        xi_leyang_logshift_two_spectrum_envelope n
  xi_leyang_logshift_two_spectrum_exponential_bound :
    ∀ n,
      xi_leyang_logshift_two_spectrum_envelope n ≤
        xi_leyang_logshift_two_spectrum_prefactor *
          xi_leyang_logshift_two_spectrum_theta ^ n

/-- The normalized two-dominant-spectrum expression near the Lee--Yang crossing. -/
def xi_leyang_logshift_two_spectrum_normalized
    (D : xi_leyang_logshift_two_spectrum_data) (n : ℕ) (x : ℝ) : ℝ :=
  (x - D.xi_leyang_logshift_two_spectrum_center) +
    D.xi_leyang_logshift_two_spectrum_remainder n

/-- Logarithmic zero equation after extracting the two dominant spectra. -/
def xi_leyang_logshift_two_spectrum_logarithmic_zero_equation
    (D : xi_leyang_logshift_two_spectrum_data) (n : ℕ) : Prop :=
  xi_leyang_logshift_two_spectrum_normalized D n
      (D.xi_leyang_logshift_two_spectrum_zero n) =
    0

/-- The quantitative distance estimate from the limiting logarithmic crossing. -/
def xi_leyang_logshift_two_spectrum_distance_estimate
    (D : xi_leyang_logshift_two_spectrum_data) (n : ℕ) : Prop :=
  |D.xi_leyang_logshift_two_spectrum_zero n -
      D.xi_leyang_logshift_two_spectrum_center| ≤
    D.xi_leyang_logshift_two_spectrum_prefactor *
      D.xi_leyang_logshift_two_spectrum_theta ^ n

/-- Paper-facing conclusion for the normalized two-spectrum reduction. -/
def xi_leyang_logshift_two_spectrum_conclusion
    (D : xi_leyang_logshift_two_spectrum_data) : Prop :=
  (∀ n, xi_leyang_logshift_two_spectrum_logarithmic_zero_equation D n) ∧
    ∀ n, xi_leyang_logshift_two_spectrum_distance_estimate D n

lemma xi_leyang_logshift_two_spectrum_logarithmic_zero_equation_proof
    (D : xi_leyang_logshift_two_spectrum_data) (n : ℕ) :
    xi_leyang_logshift_two_spectrum_logarithmic_zero_equation D n := by
  simpa [xi_leyang_logshift_two_spectrum_logarithmic_zero_equation,
    xi_leyang_logshift_two_spectrum_normalized]
    using D.xi_leyang_logshift_two_spectrum_zero_equation n

lemma xi_leyang_logshift_two_spectrum_distance_estimate_proof
    (D : xi_leyang_logshift_two_spectrum_data) (n : ℕ) :
    xi_leyang_logshift_two_spectrum_distance_estimate D n := by
  rw [xi_leyang_logshift_two_spectrum_distance_estimate]
  have hdiff :
      D.xi_leyang_logshift_two_spectrum_zero n -
          D.xi_leyang_logshift_two_spectrum_center =
        -D.xi_leyang_logshift_two_spectrum_remainder n := by
    linarith [D.xi_leyang_logshift_two_spectrum_zero_equation n]
  calc
    |D.xi_leyang_logshift_two_spectrum_zero n -
        D.xi_leyang_logshift_two_spectrum_center| =
        |-D.xi_leyang_logshift_two_spectrum_remainder n| := by rw [hdiff]
    _ = |D.xi_leyang_logshift_two_spectrum_remainder n| := by simp
    _ ≤ D.xi_leyang_logshift_two_spectrum_envelope n :=
        D.xi_leyang_logshift_two_spectrum_remainder_bound n
    _ ≤ D.xi_leyang_logshift_two_spectrum_prefactor *
        D.xi_leyang_logshift_two_spectrum_theta ^ n :=
        D.xi_leyang_logshift_two_spectrum_exponential_bound n

/-- Paper label: `thm:xi-leyang-logshift-two-spectrum`. -/
theorem paper_xi_leyang_logshift_two_spectrum
    (D : xi_leyang_logshift_two_spectrum_data) :
    xi_leyang_logshift_two_spectrum_conclusion D := by
  exact ⟨xi_leyang_logshift_two_spectrum_logarithmic_zero_equation_proof D,
    xi_leyang_logshift_two_spectrum_distance_estimate_proof D⟩

end Omega.Zeta
