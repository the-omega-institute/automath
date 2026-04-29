import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete normalized double-KL residual-rate data.  The two displayed rates are normalized by
positive factors `1 + |c|`, so each normalized rate vanishes exactly when its KL constant
vanishes. -/
structure conclusion_double_kl_residual_rate_synchronous_collapse_data where
  cuw : ℝ
  cwu : ℝ
  residualRate : ℝ
  enumerativeRate : ℝ
  residualRate_eq : residualRate = cuw / (1 + |cuw|)
  enumerativeRate_eq : enumerativeRate = cwu / (1 + |cwu|)

namespace conclusion_double_kl_residual_rate_synchronous_collapse_data

/-- The two normalized rate formulae collapse synchronously to the common baseline. -/
def synchronous_collapse
    (D : conclusion_double_kl_residual_rate_synchronous_collapse_data) : Prop :=
  D.residualRate = 0 ∧ D.enumerativeRate = 0

end conclusion_double_kl_residual_rate_synchronous_collapse_data

lemma conclusion_double_kl_residual_rate_synchronous_collapse_normalized_zero_iff
    (x r : ℝ) (hr : r = x / (1 + |x|)) : r = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hdiv : x / (1 + |x|) = 0 := by
      rw [← hr]
      exact h
    have hden : (1 + |x|) ≠ 0 := by
      have hx : 0 ≤ |x| := abs_nonneg x
      nlinarith
    have hmul := congrArg (fun y : ℝ => y * (1 + |x|)) hdiv
    simpa [hden] using hmul
  · intro hx
    simp [hr, hx]

/-- Paper label: `cor:conclusion-double-kl-residual-rate-synchronous-collapse`. -/
theorem paper_conclusion_double_kl_residual_rate_synchronous_collapse
    (D : conclusion_double_kl_residual_rate_synchronous_collapse_data) :
    (D.cuw = 0 ∧ D.cwu = 0) ↔ D.synchronous_collapse := by
  constructor
  · rintro ⟨hcuw, hcwu⟩
    exact ⟨by simp [D.residualRate_eq, hcuw], by simp [D.enumerativeRate_eq, hcwu]⟩
  · rintro ⟨hresidual, henumerative⟩
    exact
      ⟨(conclusion_double_kl_residual_rate_synchronous_collapse_normalized_zero_iff
          D.cuw D.residualRate D.residualRate_eq).mp hresidual,
        (conclusion_double_kl_residual_rate_synchronous_collapse_normalized_zero_iff
          D.cwu D.enumerativeRate D.enumerativeRate_eq).mp henumerative⟩

end Omega.Conclusion
