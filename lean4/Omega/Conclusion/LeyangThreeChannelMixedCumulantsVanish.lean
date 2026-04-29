import Omega.Conclusion.LeyangArithmeticThreeChannelExactIndependence

namespace Omega.Conclusion

noncomputable section

/-- Target-prefixed mixed cumulant readout for the centered three-channel product expansion.  A
channel contributes its centered mean when its multiplicity is positive and the unit factor
otherwise. -/
def conclusion_leyang_three_channel_mixed_cumulants_vanish_mixed_cumulant
    (f : Equiv.Perm (Fin 10) → ℝ) (g : Equiv.Perm (Fin 3) → ℝ)
    (h : Equiv.Perm (Fin 19) → ℝ) (a b c : ℕ) : ℝ :=
  (if 0 < a then
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation f
    else 1) *
    (if 0 < b then
      conclusion_leyang_arithmetic_three_channel_exact_independence_expectation g
    else 1) *
      (if 0 < c then
        conclusion_leyang_arithmetic_three_channel_exact_independence_expectation h
      else 1)

/-- Paper label: `thm:conclusion-leyang-three-channel-mixed-cumulants-vanish`. -/
theorem paper_conclusion_leyang_three_channel_mixed_cumulants_vanish
    (f : Equiv.Perm (Fin 10) → ℝ) (g : Equiv.Perm (Fin 3) → ℝ)
    (h : Equiv.Perm (Fin 19) → ℝ)
    (hf : conclusion_leyang_arithmetic_three_channel_exact_independence_expectation f = 0)
    (hg : conclusion_leyang_arithmetic_three_channel_exact_independence_expectation g = 0)
    (hh : conclusion_leyang_arithmetic_three_channel_exact_independence_expectation h = 0)
    (a b c : ℕ)
    (hmix : 2 ≤ (if 0 < a then 1 else 0) + (if 0 < b then 1 else 0) +
      (if 0 < c then 1 else 0)) :
    conclusion_leyang_three_channel_mixed_cumulants_vanish_mixed_cumulant f g h a b c = 0 := by
  have _hindependence :=
    (paper_conclusion_leyang_arithmetic_three_channel_exact_independence).2 f g h
  by_cases ha : 0 < a <;> by_cases hb : 0 < b <;> by_cases hc : 0 < c
  all_goals
    simp [conclusion_leyang_three_channel_mixed_cumulants_vanish_mixed_cumulant, ha, hb, hc,
      hf, hg, hh] at *

end

end Omega.Conclusion
