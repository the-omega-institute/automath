import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

noncomputable section

/-- The normalized positive-temperature closed form for the scalar coefficient of `β₆(q)` after
dividing numerator and denominator by `4^q`. -/
def conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_top (q : ℕ) : ℝ :=
  (1 - (1 / 2 : ℝ) ^ q) / ((1 / 2 : ℝ) ^ q * 5 + (3 / 4 : ℝ) ^ q * 4 + 9)

/-- The normalized negative-temperature closed form for the scalar coefficient of `β₆(-q)` after
dividing numerator and denominator by `2^q`. -/
def conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_bot (q : ℕ) : ℝ :=
  ((1 / 2 : ℝ) ^ q - 1) / (5 + (2 / 3 : ℝ) ^ q * 4 + (1 / 2 : ℝ) ^ q * 9)

/-- Paper-facing scalar form of the dual zero-temperature escort limit law for the window-`6`
cyclic shell. -/
def conclusion_window6_cyclic_escort_dual_zero_temp_statement : Prop :=
  conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_top 0 = 0 ∧
    Tendsto conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_top atTop (𝓝 (1 / 9 : ℝ)) ∧
    Tendsto conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_bot atTop (𝓝 (-1 / 5 : ℝ))

/-- Paper label: `cor:conclusion-window6-cyclic-escort-dual-zero-temp`. The normalized closed
forms obtained by dividing the positive branch by `4^q` and the negative branch by `2^q` have the
stated endpoint values and zero-temperature limits. -/
theorem paper_conclusion_window6_cyclic_escort_dual_zero_temp :
    conclusion_window6_cyclic_escort_dual_zero_temp_statement := by
  have hhalf :
      Tendsto (fun q : ℕ => (1 / 2 : ℝ) ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hthreequarters :
      Tendsto (fun q : ℕ => (3 / 4 : ℝ) ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have htwothirds :
      Tendsto (fun q : ℕ => (2 / 3 : ℝ) ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨by simp [conclusion_window6_cyclic_escort_dual_zero_temp_beta_at_top], ?_, ?_⟩
  · have hnum :
        Tendsto (fun q : ℕ => 1 - (1 / 2 : ℝ) ^ q) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub hhalf
    have hden0 :
        Tendsto
          (fun q : ℕ => 5 * (1 / 2 : ℝ) ^ q + 4 * (3 / 4 : ℝ) ^ q + 9)
          atTop (𝓝 (9 : ℝ)) := by
      simpa using ((hhalf.const_mul 5).add (hthreequarters.const_mul 4)).add tendsto_const_nhds
    have hden :
        Tendsto
          (fun q : ℕ => (1 / 2 : ℝ) ^ q * 5 + (3 / 4 : ℝ) ^ q * 4 + 9)
          atTop (𝓝 (9 : ℝ)) := by
      convert hden0 using 1 <;> funext q <;> ring
    exact hnum.div hden (by norm_num : (9 : ℝ) ≠ 0)
  · have hnum :
        Tendsto (fun q : ℕ => (1 / 2 : ℝ) ^ q - 1) atTop (𝓝 (-1 : ℝ)) := by
      simpa using hhalf.sub tendsto_const_nhds
    have hden0 :
        Tendsto
          (fun q : ℕ => 5 + 4 * (2 / 3 : ℝ) ^ q + 9 * (1 / 2 : ℝ) ^ q)
          atTop (𝓝 (5 : ℝ)) := by
      simpa [add_assoc] using
        tendsto_const_nhds.add ((htwothirds.const_mul 4).add (hhalf.const_mul 9))
    have hden :
        Tendsto
          (fun q : ℕ => 5 + (2 / 3 : ℝ) ^ q * 4 + (1 / 2 : ℝ) ^ q * 9)
          atTop (𝓝 (5 : ℝ)) := by
      convert hden0 using 1 <;> funext q <;> ring
    exact hnum.div hden (by norm_num : (5 : ℝ) ≠ 0)

end

end Omega.Conclusion
