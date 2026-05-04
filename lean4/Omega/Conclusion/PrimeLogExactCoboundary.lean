import Mathlib.Tactic
import Omega.Conclusion.PrimeLogZeroLyapunovCalibration

namespace Omega.Conclusion

noncomputable section

/-- The exact coboundary package extracted from the zero-Lyapunov calibration recurrence.
The potential `logM` is cohomologous to the negative defect `δ`; exponentiating gives the
corresponding multiplicative identity, and the defect bounds are inherited from the calibrated
prime-log recurrence. -/
def conclusion_prime_log_exact_coboundary_statement : Prop :=
  ∀ (c : ℝ) (w δ S logM : ℕ → ℝ),
    0 < c →
      (∀ j, 1 ≤ j → c < w j ∧ w j < w (j + 1)) →
        δ 0 = 0 →
          (∀ j, 1 ≤ j →
            ((δ (j - 1) + c < w j ∧ δ j = δ (j - 1) + c) ∨
              (w j ≤ δ (j - 1) + c ∧ δ j = δ (j - 1) + c - w j))) →
            (∀ j, 1 ≤ j → δ j = c * (j : ℝ) - S j) →
              (∀ j, 1 ≤ j → logM j = S j - c * (j : ℝ)) →
                (∀ j, 1 ≤ j → logM j = -δ j) ∧
                  (∀ j, 1 ≤ j → Real.exp (logM j) = Real.exp (-δ j)) ∧
                    (∀ j, 1 ≤ j → 0 ≤ δ j ∧ δ j < w j) ∧
                      (∀ j, 1 ≤ j → -w (j + 1) < logM j ∧ logM j ≤ 0)

/-- Paper label: `thm:conclusion-prime-log-exact-coboundary`. -/
theorem paper_conclusion_prime_log_exact_coboundary :
    conclusion_prime_log_exact_coboundary_statement := by
  intro c w δ S logM hc hw hδ0 hstep hS hlogM
  rcases paper_conclusion_prime_log_calibration_zero_lyapunov_product
      c w δ S logM hc hw hδ0 hstep hS hlogM with
    ⟨hδ_bounds, _hS_bounds, hlogM_bounds⟩
  have hcoboundary : ∀ j, 1 ≤ j → logM j = -δ j := by
    intro j hj
    have hδj := hS j hj
    have hlogj := hlogM j hj
    linarith
  refine ⟨hcoboundary, ?_, hδ_bounds, hlogM_bounds⟩
  intro j hj
  rw [hcoboundary j hj]

end
end Omega.Conclusion
