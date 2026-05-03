import Mathlib.Tactic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Omega.Conclusion

open Filter
open scoped Topology

noncomputable section

/-- Shared quartic coefficient for a Poisson coarse-grained smooth `f`-divergence expansion. -/
def conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
    (secondMoment localSecondDerivative : ℝ) : ℝ :=
  localSecondDerivative * secondMoment ^ (2 : ℕ) / 8

/-- Abstract asymptotic-ratio form of the universal Poisson `f`-divergence theorem.  The two
normalized divergences converge to quartic coefficients with the same nonzero second moment, so
their quotient keeps only the ratio of the local second derivatives. -/
def conclusion_poisson_fdivergence_universal_ratio_statement : Prop :=
  ∀ (F G : ℕ → ℝ) (secondMoment fSecond gSecond : ℝ),
    secondMoment ≠ 0 →
      gSecond ≠ 0 →
        Tendsto F atTop
            (𝓝 (conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
              secondMoment fSecond)) →
          Tendsto G atTop
            (𝓝 (conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
              secondMoment gSecond)) →
            (∀ᶠ n in atTop, G n ≠ 0) →
              Tendsto (fun n : ℕ => F n / G n) atTop (𝓝 (fSecond / gSecond))

theorem paper_conclusion_poisson_fdivergence_universal_ratio :
    conclusion_poisson_fdivergence_universal_ratio_statement := by
  intro F G secondMoment fSecond gSecond hmoment hgSecond hF hG _hG_ne
  have hden :
      conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
        secondMoment gSecond ≠ 0 := by
    unfold conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
    exact div_ne_zero (mul_ne_zero hgSecond (pow_ne_zero (2 : ℕ) hmoment)) (by norm_num)
  have hratio :
      Tendsto (fun n : ℕ => F n / G n) atTop
        (𝓝
          (conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
              secondMoment fSecond /
            conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
              secondMoment gSecond)) :=
    hF.div hG hden
  have hsimplify :
      conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
          secondMoment fSecond /
        conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
          secondMoment gSecond =
        fSecond / gSecond := by
    unfold conclusion_poisson_fdivergence_universal_ratio_quartic_coefficient
    field_simp [hmoment, hgSecond, pow_ne_zero (2 : ℕ) hmoment]
  simpa [hsimplify] using hratio

end

end Omega.Conclusion
