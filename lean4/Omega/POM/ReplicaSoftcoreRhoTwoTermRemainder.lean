import Omega.POM.ReplicaSoftcorePerronFibonacciFixedPoint
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-replica-softcore-rho-two-term-remainder`. -/
theorem paper_pom_replica_softcore_rho_two_term_remainder (q : Nat) (hq : 2 ≤ q)
    (rho : ℝ)
    (hrho : pom_replica_softcore_perron_fibonacci_fixed_point_is_perron_root q rho) :
    ∃ Rq : ℝ,
      rho = (2 : ℝ) ^ (q - 1) + (3 : ℝ) ^ q / (2 : ℝ) ^ (q + 1) + Rq ∧
        0 < Rq := by
  refine ⟨rho - (2 : ℝ) ^ (q - 1) - (3 : ℝ) ^ q / (2 : ℝ) ^ (q + 1), ?_, ?_⟩
  · ring
  · have hrho_eq : rho = (2 : ℝ) ^ (q - 1) * 2 := by
      simpa [pom_replica_softcore_perron_fibonacci_fixed_point_is_perron_root,
        pom_replica_softcore_perron_fibonacci_fixed_point_value, hq] using hrho
    have hq_ne : q ≠ 0 := by omega
    have hpow_lt : (3 : ℝ) ^ q < (4 : ℝ) ^ q := by
      exact pow_lt_pow_left₀ (by norm_num : (3 : ℝ) < 4) (by norm_num : (0 : ℝ) ≤ 3)
        hq_ne
    have hden_pos : 0 < (2 : ℝ) ^ (q + 1) := by positivity
    have hscaled :
        (3 : ℝ) ^ q / (2 : ℝ) ^ (q + 1) < (2 : ℝ) ^ (q - 1) := by
      rw [div_lt_iff₀ hden_pos]
      have hpow_split : (2 : ℝ) ^ (q - 1) * (2 : ℝ) ^ (q + 1) = (4 : ℝ) ^ q := by
        rw [← pow_add]
        have hsum : (q - 1) + (q + 1) = 2 * q := by omega
        rw [hsum, pow_mul]
        norm_num
      simpa [hpow_split] using hpow_lt
    rw [hrho_eq]
    nlinarith

end Omega.POM
