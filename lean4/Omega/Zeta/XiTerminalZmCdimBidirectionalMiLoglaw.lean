import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Explicit entropy window coming from the standard `n^d` counting and cylinder estimates. -/
def xi_terminal_zm_cdim_bidirectional_mi_loglaw_entropy_window
    (d : ℕ) (massConst wordConst : ℝ) (n : ℕ) : Prop :=
  (d : ℝ) * Real.log n - Real.log massConst ≤
    (d : ℝ) * Real.log n + Real.log wordConst

/-- Explicit mutual-information window obtained from `I_n = 2 H_n - H_{2n}`. -/
def xi_terminal_zm_cdim_bidirectional_mi_loglaw_mutual_information_window
    (d : ℕ) (massConst wordConst : ℝ) (n : ℕ) (I : ℕ → ℝ) : Prop :=
  (d : ℝ) * Real.log n -
      (2 * Real.log massConst + Real.log wordConst + (d : ℝ) * Real.log 2) ≤ I n ∧
    I n ≤ (d : ℝ) * Real.log n + (2 * Real.log wordConst + Real.log massConst)

/-- The entropy-counting argument and the cylinder-measure lower bound are packaged here as the
two-sided `d log n + O(1)` entropy window; applying `I_n = 2 H_n - H_{2n}` then gives the same
logarithmic window for bidirectional mutual information.
    thm:xi-terminal-zm-cdim-bidirectional-mi-loglaw -/
theorem paper_xi_terminal_zm_cdim_bidirectional_mi_loglaw
    (d : ℕ) (entropy mutualInformation : ℕ → ℝ) (wordConst massConst : ℝ)
    (hentropyLower :
      ∀ n : ℕ, 1 ≤ n → (d : ℝ) * Real.log n - Real.log massConst ≤ entropy n)
    (hentropyUpper :
      ∀ n : ℕ, 1 ≤ n → entropy n ≤ (d : ℝ) * Real.log n + Real.log wordConst)
    (hchain : ∀ n, 1 ≤ n → mutualInformation n = 2 * entropy n - entropy (2 * n)) :
    ∀ n, 1 ≤ n →
      xi_terminal_zm_cdim_bidirectional_mi_loglaw_entropy_window d massConst wordConst n ∧
      xi_terminal_zm_cdim_bidirectional_mi_loglaw_mutual_information_window
        d massConst wordConst n mutualInformation := by
  intro n hn
  have hwindow :
      xi_terminal_zm_cdim_bidirectional_mi_loglaw_entropy_window d massConst wordConst n := by
    dsimp [xi_terminal_zm_cdim_bidirectional_mi_loglaw_entropy_window]
    linarith [hentropyLower n hn, hentropyUpper n hn]
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog_two_mul :
      Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hn_real)]
  have hmi_window :
      xi_terminal_zm_cdim_bidirectional_mi_loglaw_mutual_information_window
        d massConst wordConst n mutualInformation := by
    dsimp [xi_terminal_zm_cdim_bidirectional_mi_loglaw_mutual_information_window]
    have hn2 : 1 ≤ 2 * n := by omega
    have hupper2 := hentropyUpper (2 * n) hn2
    have hlower2 := hentropyLower (2 * n) hn2
    have hlog_two_mul_nat : Real.log (2 * n) = Real.log 2 + Real.log n := by
      simpa using hlog_two_mul
    have hupper2' :
        entropy (2 * n) ≤ (d : ℝ) * (Real.log 2 + Real.log n) + Real.log wordConst := by
      simpa [hlog_two_mul_nat] using hupper2
    have hlower2' :
        (d : ℝ) * (Real.log 2 + Real.log n) - Real.log massConst ≤ entropy (2 * n) := by
      simpa [hlog_two_mul_nat] using hlower2
    have hlower2_weakened :
        (d : ℝ) * Real.log n - Real.log massConst ≤ entropy (2 * n) := by
      have hlog2_nonneg : 0 ≤ (d : ℝ) * Real.log 2 := by
        have hd_nonneg : 0 ≤ (d : ℝ) := by exact_mod_cast Nat.zero_le d
        have hlog2_nonneg' : 0 ≤ Real.log 2 := by
          have hlog2_pos : 0 < Real.log 2 := by
            exact Real.log_pos (by norm_num)
          linarith
        nlinarith
      linarith [hlower2', hlog2_nonneg]
    rw [hchain n hn]
    constructor
    · linarith [hentropyLower n hn, hentropyLower n hn, hupper2']
    · linarith [hentropyUpper n hn, hentropyUpper n hn, hlower2_weakened]
  exact ⟨hwindow, hmi_window⟩

end Omega.Zeta
