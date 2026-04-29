import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The pointwise code-length overhead over entropy. -/
def xi_terminal_zm_godel_prefix_code_mi_difference_error
    (H L : ℕ → ℝ) (n : ℕ) : ℝ :=
  L n - H n

/-- Paper label: `prop:xi-terminal-zm-godel-prefix-code-mi-difference`. -/
theorem paper_xi_terminal_zm_godel_prefix_code_mi_difference
    (H L I : ℕ → ℝ) (n : ℕ)
    (hLower : ∀ m, H m ≤ L m)
    (hUpper : ∀ m, L m ≤ H m + Real.log 2)
    (hMutualInformation : ∀ m, I m = 2 * H m - H (2 * m)) :
    |I n - (2 * L n - L (2 * n))| ≤ 3 * Real.log 2 := by
  let e : ℕ → ℝ := xi_terminal_zm_godel_prefix_code_mi_difference_error H L
  have he_nonneg : 0 ≤ e n := by
    dsimp [e, xi_terminal_zm_godel_prefix_code_mi_difference_error]
    exact sub_nonneg.mpr (hLower n)
  have he_upper : e n ≤ Real.log 2 := by
    dsimp [e, xi_terminal_zm_godel_prefix_code_mi_difference_error]
    linarith [hUpper n]
  have he2_nonneg : 0 ≤ e (2 * n) := by
    dsimp [e, xi_terminal_zm_godel_prefix_code_mi_difference_error]
    exact sub_nonneg.mpr (hLower (2 * n))
  have he2_upper : e (2 * n) ≤ Real.log 2 := by
    dsimp [e, xi_terminal_zm_godel_prefix_code_mi_difference_error]
    linarith [hUpper (2 * n)]
  have he_abs : |e n| ≤ Real.log 2 := by
    rw [abs_of_nonneg he_nonneg]
    exact he_upper
  have he2_abs : |e (2 * n)| ≤ Real.log 2 := by
    rw [abs_of_nonneg he2_nonneg]
    exact he2_upper
  have hrewrite : I n - (2 * L n - L (2 * n)) = e (2 * n) - 2 * e n := by
    dsimp [e, xi_terminal_zm_godel_prefix_code_mi_difference_error]
    rw [hMutualInformation n]
    ring
  rw [hrewrite]
  refine abs_le.mpr ?_
  constructor <;> linarith

end Omega.Zeta
