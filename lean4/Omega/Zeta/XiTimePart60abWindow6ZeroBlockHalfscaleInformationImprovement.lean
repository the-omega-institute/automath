import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Folding.FoldZeroHalfIndexMultiple6

namespace Omega.Zeta

private lemma xi_time_part60ab_window6_zero_block_halfscale_information_improvement_neg_log_lower
    {u : ℝ} (hu1 : u < 1) :
    u ≤ -Real.log (1 - u) := by
  have hpos : 0 < 1 - u := by linarith
  have hlog : Real.log (1 - u) ≤ (1 - u) - 1 := Real.log_le_sub_one_of_pos hpos
  linarith

/-- The normalized half-scale Fibonacci density coming from the window-`6` zero-block lower bound
`|Z_{6n+4}| ≥ F_{3n+3}` and `|X_{6n+4}| = F_{6n+6}`. -/
noncomputable def xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density
    (n : ℕ) : ℝ :=
  (Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6)

/-- Paper label: `thm:xi-time-part60ab-window6-zero-block-halfscale-information-improvement`.
On the rigid window-`6` subsequence, the half-scale Fibonacci lower bound gives a concrete
collision-density improvement, and because this density stays below `1`, the basic logarithmic
defect inequality upgrades it to a positive KL-type improvement. -/
theorem paper_xi_time_part60ab_window6_zero_block_halfscale_information_improvement :
    (∀ n,
      xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n ≤
        ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℝ) / Nat.fib (6 * n + 6)) ∧
      (∀ n, xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n < 1) ∧
      (∀ n,
        xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n ≤
          -Real.log
            (1 -
              xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n)) := by
  have hlower :
      ∀ n,
        xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n ≤
          ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℝ) / Nat.fib (6 * n + 6) := by
    intro n
    have hlow := (Omega.Folding.paper_fold_zero_half_index_multiple6 (6 * n + 4) (by omega)).2
    have hden_nonneg : 0 ≤ (Nat.fib (6 * n + 6) : ℝ) := by positivity
    have hidx : (6 * n + 4 + 2) / 2 = 3 * n + 3 := by omega
    have hlow_real :
        (Nat.fib (3 * n + 3) : ℝ) ≤
          ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℝ) := by
      simpa [hidx] using (show (Nat.fib ((6 * n + 4 + 2) / 2) : ℝ) ≤
        ((Omega.Folding.foldZeroFrequencyUnion (6 * n + 4)).card : ℝ) by exact_mod_cast hlow)
    simpa [xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density] using
      div_le_div_of_nonneg_right hlow_real hden_nonneg
  have hlt :
      ∀ n, xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n < 1 := by
    intro n
    have hstep : Nat.fib (3 * n + 3) < Nat.fib (3 * n + 4) := by
      exact Nat.fib_lt_fib_succ (by omega)
    have hmono : Nat.fib (3 * n + 4) ≤ Nat.fib (6 * n + 6) := Nat.fib_mono (by omega)
    have hstrict : Nat.fib (3 * n + 3) < Nat.fib (6 * n + 6) := lt_of_lt_of_le hstep hmono
    have hden_pos : 0 < (Nat.fib (6 * n + 6) : ℝ) := by
      exact_mod_cast Nat.fib_pos.mpr (by omega)
    have hstrict_real : (Nat.fib (3 * n + 3) : ℝ) < Nat.fib (6 * n + 6) := by
      exact_mod_cast hstrict
    have hratio :
        (Nat.fib (3 * n + 3) : ℝ) / Nat.fib (6 * n + 6) < 1 := by
      simpa using div_lt_div_of_pos_right hstrict_real hden_pos
    simpa [xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density] using
      hratio
  have hkl :
      ∀ n,
        xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n ≤
          -Real.log
            (1 -
              xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n) := by
    intro n
    have hnonneg :
        0 ≤ xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density n := by
      unfold xi_time_part60ab_window6_zero_block_halfscale_information_improvement_density
      positivity
    exact
      xi_time_part60ab_window6_zero_block_halfscale_information_improvement_neg_log_lower
        (hlt n)
  exact ⟨hlower, hlt, hkl⟩

end Omega.Zeta
