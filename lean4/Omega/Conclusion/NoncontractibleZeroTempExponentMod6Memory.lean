import Omega.Conclusion.NoncontractibleLossMod6Explicit
import Omega.DerivedConsequences.DerivedMaxNoncontractibleFiberNoExponentialPenalty
import Omega.POM.ZeroTemperatureTwoTermExpansion

namespace Omega.Conclusion

/-- Conclusion-facing package combining the zero-temperature seeds, the common exponential-rate
comparison, and the explicit mod-`6` noncontractible memory formula. -/
def conclusion_noncontractible_zero_temp_exponent_mod6_memory_statement : Prop :=
  (∀ q : ℕ, (q + 1 : ℤ) * 1 - q = 1) ∧
    ((2 : ℕ) ^ 5 / 2 ^ 5 = 1) ∧
    (∃ c C : ℚ,
      0 < c ∧
        c ≤ C ∧
        (∀ k : ℕ,
          9 ≤ k →
            c ≤ (noncontractibleFiberCount (2 * k) : ℚ) / noncontractibleMainFiberCount (2 * k) ∧
              (noncontractibleFiberCount (2 * k) : ℚ) /
                  noncontractibleMainFiberCount (2 * k) ≤
                C) ∧
        (∀ k : ℕ,
          8 ≤ k →
            c ≤
                  (noncontractibleFiberCount (2 * k + 1) : ℚ) /
                    noncontractibleMainFiberCount (2 * k + 1) ∧
              (noncontractibleFiberCount (2 * k + 1) : ℚ) /
                  noncontractibleMainFiberCount (2 * k + 1) ≤
                C) ∧
        Real.log (Real.sqrt Real.goldenRatio) = (1 / 2 : ℝ) * Real.log Real.goldenRatio) ∧
    (∀ m : ℕ,
      noncontractibleLoss m =
        if m % 6 = 0 ∨ m % 6 = 4 then Real.log (noncontractibleMainFiberCount m)
        else if m % 6 = 1 ∨ m % 6 = 5 then Real.log (noncontractibleSecondFiberCount m)
        else Real.log (noncontractibleThirdFiberCount m))

/-- Paper label: `thm:conclusion-noncontractible-zero-temp-exponent-mod6-memory`. -/
theorem paper_conclusion_noncontractible_zero_temp_exponent_mod6_memory :
    conclusion_noncontractible_zero_temp_exponent_mod6_memory_statement := by
  have hzeroTemp := Omega.POM.paper_pom_zero_temperature_two_term_expansion_maxfiber_entropy
  have hrate := Omega.DerivedConsequences.paper_derived_max_noncontractible_fiber_no_exponential_penalty
  have hmod6 := paper_conclusion_noncontractible_loss_mod6_explicit
  refine ⟨hzeroTemp.1, hzeroTemp.2.1, hrate, hmod6.2.2⟩

end Omega.Conclusion
