import Omega.Zeta.XiTimePart70OddPrimeRhDefectSummableMass

namespace Omega.Zeta

noncomputable section

/-- Concrete input package for transferring the odd-prime defect comparison to a powered tail. -/
structure xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold_data where
  isOddPrime : ℕ → Prop
  defect : ℕ → ℝ
  alpha : ℝ
  p0 : ℕ
  C : ℝ
  p0_pos : 1 ≤ p0
  C_nonneg : 0 ≤ C
  alpha_threshold : (1 / 2 : ℝ) < alpha
  defect_nonneg : ∀ n, isOddPrime n → p0 ≤ n → 0 ≤ defect n
  powered_defect_bound :
    ∀ n, isOddPrime n → p0 ≤ n → defect n ^ alpha ≤ C / (n : ℝ) ^ 2

/-- The powered odd-prime defect tail is summable. -/
def xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold_statement
    (D : xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold_data) : Prop := by
  classical
  exact Summable (fun n : ℕ => if D.isOddPrime n then D.defect n ^ D.alpha else 0)

/-- Paper label: `thm:xi-time-part70-odd-prime-rh-defect-ell-alpha-threshold`. -/
theorem paper_xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold
    (D : xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold_data) :
    xi_time_part70_odd_prime_rh_defect_ell_alpha_threshold_statement D := by
  classical
  exact paper_xi_time_part70_odd_prime_rh_defect_summable_mass
    D.isOddPrime
    (fun n : ℕ => D.defect n ^ D.alpha)
    D.p0
    D.C
    D.p0_pos
    D.C_nonneg
    (by
      intro n hn htail
      exact Real.rpow_nonneg (D.defect_nonneg n hn htail) D.alpha)
    D.powered_defect_bound

end

end Omega.Zeta
