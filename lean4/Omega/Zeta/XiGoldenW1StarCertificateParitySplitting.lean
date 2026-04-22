import Mathlib.Tactic
import Omega.Kronecker.W1RightShiftedMinimizer
import Omega.Zeta.XiGoldenW1TrueTwoPhaseLimit

namespace Omega.Zeta

/-- Paper label: `thm:xi-golden-w1-star-certificate-parity-splitting`.
For Fibonacci denominators, the even-index branch lies on the bad side where the `W₁` certificate
is exactly half the star-discrepancy certificate, while the odd-index branch lies on the good side
where the star value freezes at `1 / F_n`. The odd branch also carries the previously established
golden subsequential `W₁` limit constant. -/
theorem paper_xi_golden_w1_star_certificate_parity_splitting :
    (∀ n : ℕ, 3 ≤ n → Even n → ∀ δ : ℚ, δ < 0 →
      let q := Nat.fib n
      Omega.Kronecker.kroneckerBadSideStarDiscrepancy q δ ≠ 0 ∧
        2 * Omega.Kronecker.kroneckerBadSideW1 q δ =
          Omega.Kronecker.kroneckerBadSideStarDiscrepancy q δ) ∧
    (∀ n : ℕ, 3 ≤ n → Odd n →
      Omega.Kronecker.kroneckerGoodSideStarDiscrepancy (Nat.fib n) = (1 : ℚ) / Nat.fib n) ∧
    Omega.Kronecker.goldenOddScaledLimitConstant =
      (1 / 2 : ℝ) - 1 / (2 * Real.sqrt 5) + 1 / 15 := by
  rcases paper_xi_golden_w1_true_two_phase_limit with ⟨_, _, hodd, _, _, _⟩
  refine ⟨?_, ?_, hodd⟩
  · intro n hn hEven δ hδ
    let q := Nat.fib n
    have hq : 2 ≤ q := by
      have hbase : 2 ≤ Nat.fib 3 := by native_decide
      exact le_trans hbase (Nat.fib_mono hn)
    rcases Omega.Kronecker.paper_xi_kronecker_star_discrepancy_w1_branching q hq with
      ⟨hbad, _, _, _, _⟩
    rcases hbad δ hδ with ⟨hstar_formula, hw1_eq⟩
    have hq_pos : (0 : ℚ) < q := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hq)
    have hstar_pos : 0 < Omega.Kronecker.kroneckerBadSideStarDiscrepancy q δ := by
      rw [hstar_formula]
      have hterm_nonneg : 0 ≤ ((q - 1 : ℕ) : ℚ) * (-δ) := by
        have : 0 ≤ -δ := by linarith
        positivity
      have hrecip_pos : 0 < (1 : ℚ) / q := by
        exact div_pos (by norm_num) hq_pos
      linarith
    have hstar_ne : Omega.Kronecker.kroneckerBadSideStarDiscrepancy q δ ≠ 0 :=
      ne_of_gt hstar_pos
    refine ⟨hstar_ne, ?_⟩
    linarith [hw1_eq]
  · intro n hn hOdd
    let q := Nat.fib n
    have hq : 2 ≤ q := by
      have hbase : 2 ≤ Nat.fib 3 := by native_decide
      exact le_trans hbase (Nat.fib_mono hn)
    rcases Omega.Kronecker.paper_xi_kronecker_star_discrepancy_w1_branching q hq with
      ⟨_, hgood, _, _, _⟩
    simpa using (hgood 1 (by norm_num : (0 : ℚ) < 1)).1

end Omega.Zeta
