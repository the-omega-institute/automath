import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-equal-shell-variance-gap-identity`. -/
theorem paper_conclusion_equal_shell_variance_gap_identity (n : ℕ) (m : Fin n → ℕ)
    (xj : Fin n → ℝ) (hM : 0 < ∑ j, (m j : ℝ)) :
    let M : ℝ := ∑ j, (m j : ℝ)
    let xbar : ℝ := -(∑ j, (m j : ℝ) * xj j) / M
    (∑ j, (m j : ℝ) * (xj j) ^ 2 / 2) - M * xbar ^ 2 / 2 =
      (M / 2) * (((∑ j, (m j : ℝ) * (xj j) ^ 2) / M) - xbar ^ 2) := by
  dsimp
  set M : ℝ := ∑ j, (m j : ℝ)
  set S : ℝ := ∑ j, (m j : ℝ) * (xj j) ^ 2
  set A : ℝ := ∑ j, (m j : ℝ) * xj j
  have hM0 : M ≠ 0 := by
    subst M
    linarith
  have hcalc :
      S / 2 - M * (-A / M) ^ 2 / 2 = (M / 2) * (S / M - (-A / M) ^ 2) := by
    field_simp [hM0]
  have hS : (∑ j, (m j : ℝ) * (xj j) ^ 2 / 2) = S / 2 := by
    rw [← Finset.sum_div]
  calc
    (∑ j, (m j : ℝ) * (xj j) ^ 2 / 2) - (∑ j, (m j : ℝ)) * ((-(∑ j, (m j : ℝ) * xj j)) /
        (∑ j, (m j : ℝ))) ^ 2 / 2
        = S / 2 - M * (-A / M) ^ 2 / 2 := by simp [hS, M, A]
    _ = (M / 2) * (S / M - (-A / M) ^ 2) := hcalc
    _ = ((∑ j, (m j : ℝ)) / 2) *
        (((∑ j, (m j : ℝ) * (xj j) ^ 2) / (∑ j, (m j : ℝ))) -
          ((-(∑ j, (m j : ℝ) * xj j)) / (∑ j, (m j : ℝ))) ^ 2) := by
          simp [M, S, A]

end Omega.Conclusion
