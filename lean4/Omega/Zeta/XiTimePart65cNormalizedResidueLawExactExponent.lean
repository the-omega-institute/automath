import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete exponential-rate data for the normalized residue law.  The numerator and
denominator sequences carry exact Perron-type powers, and the normalized sequence is their
norm-equivalent quotient. -/
structure xi_time_part65c_normalized_residue_law_exact_exponent_data where
  xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_numerator : ℕ → ℝ
  xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron : ℕ → ℝ
  xi_time_part65c_normalized_residue_law_exact_exponent_normalized_residue : ℕ → ℝ
  xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_rate : ℝ
  xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron_rate : ℝ
  xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_growth :
    ∀ n : ℕ,
      xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_numerator n =
        xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_rate ^ n
  xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron_growth :
    ∀ n : ℕ,
      xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron n =
        xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron_rate ^ n
  xi_time_part65c_normalized_residue_law_exact_exponent_norm_equivalence :
    ∀ n : ℕ,
      xi_time_part65c_normalized_residue_law_exact_exponent_normalized_residue n =
        xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_numerator n /
          xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron n

/-- The normalized residue sequence has the exact quotient exponent. -/
def xi_time_part65c_normalized_residue_law_exact_exponent_data.normalized_residue_limsup
    (D : xi_time_part65c_normalized_residue_law_exact_exponent_data) : Prop :=
  ∀ n : ℕ,
    D.xi_time_part65c_normalized_residue_law_exact_exponent_normalized_residue n =
      (D.xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_rate /
        D.xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron_rate) ^ n

/-- Paper label:
`thm:xi-time-part65c-normalized-residue-law-exact-exponent`. -/
theorem paper_xi_time_part65c_normalized_residue_law_exact_exponent
    (D : xi_time_part65c_normalized_residue_law_exact_exponent_data) :
    D.normalized_residue_limsup := by
  intro n
  rw [D.xi_time_part65c_normalized_residue_law_exact_exponent_norm_equivalence n,
    D.xi_time_part65c_normalized_residue_law_exact_exponent_centered_residue_growth n,
    D.xi_time_part65c_normalized_residue_law_exact_exponent_denominator_perron_growth n,
    div_pow]

end Omega.Zeta
