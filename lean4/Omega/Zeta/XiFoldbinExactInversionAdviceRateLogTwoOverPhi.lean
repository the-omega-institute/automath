import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete data for the bin-fold exact inversion advice-rate theorem. -/
structure xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data where
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_K : ℕ → ℕ
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_L : ℕ → ℕ
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin : ℕ → ℕ
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_fib : ℕ → ℕ
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_L_eq :
    ∀ m : ℕ,
      xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_L m =
        xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_K m - m
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_lower :
    ∀ m : ℕ,
      (m : ℝ) -
          Real.log
              (xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_fib (m + 2) : ℝ) /
            Real.log 2 ≤
        xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_upper :
    ∀ m : ℕ,
      (xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m : ℝ) ≤
        Nat.ceil
          (Real.log
              (xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_fib
                (xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_L m + 2) : ℝ) /
            Real.log 2)
  xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_rate_bound :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ m : ℕ,
          |(xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m : ℝ) -
              (Real.log (2 / Real.goldenRatio) / Real.log 2) * (m : ℝ)| ≤ C

namespace xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data

/-- Base-two logarithm of the packaged Fibonacci-cardinality model. -/
def xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_log2Fib
    (D : xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data) (n : ℕ) : ℝ :=
  Real.log (D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_fib n : ℝ) /
    Real.log 2

/-- The limiting advice-bit rate `log₂(2 / φ)`. -/
def xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_rate
    (_D : xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data) : ℝ :=
  Real.log (2 / Real.goldenRatio) / Real.log 2

/-- Statement of the exact inversion advice-rate theorem. -/
def xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_statement
    (D : xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data) : Prop :=
  (∀ m : ℕ,
      (m : ℝ) - D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_log2Fib (m + 2) ≤
        D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m) ∧
    (∀ m : ℕ,
      (D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m : ℝ) ≤
        Nat.ceil
          (D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_log2Fib
            (D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_L m + 2))) ∧
    (∃ C : ℝ,
      0 ≤ C ∧
        ∀ m : ℕ,
          |(D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_Bmin m : ℝ) -
              D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_rate * (m : ℝ)| ≤ C)

end xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data

open xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data

/-- Paper label: `thm:xi-foldbin-exact-inversion-advice-rate-log-two-over-phi`. -/
theorem paper_xi_foldbin_exact_inversion_advice_rate_log_two_over_phi
    (D : xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_data) :
    xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_statement D := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    simpa [xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_log2Fib] using
      D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_lower m
  · intro m
    simpa [xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_log2Fib] using
      D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_upper m
  · simpa [xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_rate] using
      D.xi_foldbin_exact_inversion_advice_rate_log_two_over_phi_rate_bound

end

end Omega.Zeta
