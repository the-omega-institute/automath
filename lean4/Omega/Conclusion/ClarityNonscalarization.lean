import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Conclusion

/-- Concrete asymptotic-rate data for `thm:conclusion-clarity-nonscalarization`. -/
structure conclusion_clarity_nonscalarization_data where
  conclusion_clarity_nonscalarization_lowExponent : ℝ
  conclusion_clarity_nonscalarization_highExponent : ℝ
  conclusion_clarity_nonscalarization_strictGap :
    conclusion_clarity_nonscalarization_lowExponent <
      conclusion_clarity_nonscalarization_highExponent

namespace conclusion_clarity_nonscalarization_data

/-- The exponential ratio between the two indicator ambiguity observables. -/
noncomputable def indicatorRatio (D : conclusion_clarity_nonscalarization_data) (n : ℕ) : ℝ :=
  Real.exp
    ((D.conclusion_clarity_nonscalarization_highExponent -
        D.conclusion_clarity_nonscalarization_lowExponent) *
      (n : ℝ))

/-- The slower-decaying ambiguity indicator, normalized as the ratio channel. -/
noncomputable def conclusion_clarity_nonscalarization_indicatorLow
    (D : conclusion_clarity_nonscalarization_data) (n : ℕ) : ℝ :=
  D.indicatorRatio n

/-- The faster-decaying ambiguity indicator after quotient normalization. -/
noncomputable def conclusion_clarity_nonscalarization_indicatorHigh
    (_D : conclusion_clarity_nonscalarization_data) (_n : ℕ) : ℝ :=
  1

/-- A single scalar normalization would make both indicator observables converge to nonzero
finite constants after division by the same scalar sequence. -/
def conclusion_clarity_nonscalarization_commonScalarNormalization
    (D : conclusion_clarity_nonscalarization_data) : Prop :=
  ∃ C : ℕ → ℝ,
    (∀ n, C n ≠ 0) ∧
      ∃ cLow cHigh : ℝ,
        cLow ≠ 0 ∧
          cHigh ≠ 0 ∧
            Tendsto
              (fun n => D.conclusion_clarity_nonscalarization_indicatorLow n / C n)
              atTop (𝓝 cLow) ∧
              Tendsto
                (fun n => D.conclusion_clarity_nonscalarization_indicatorHigh n / C n)
                atTop (𝓝 cHigh)

/-- No nonzero scalar sequence normalizes all monotone ambiguity indicators at once. -/
def noUniversalScalar (D : conclusion_clarity_nonscalarization_data) : Prop :=
  ¬ D.conclusion_clarity_nonscalarization_commonScalarNormalization

/-- The two indicator ambiguity observables have exponentially divergent ratio. -/
def indicatorRatioDiverges (D : conclusion_clarity_nonscalarization_data) : Prop :=
  Tendsto D.indicatorRatio atTop atTop

lemma conclusion_clarity_nonscalarization_indicatorRatio_tendsto
    (D : conclusion_clarity_nonscalarization_data) :
    D.indicatorRatioDiverges := by
  have hgap :
      0 <
        D.conclusion_clarity_nonscalarization_highExponent -
          D.conclusion_clarity_nonscalarization_lowExponent := by
    exact sub_pos.mpr D.conclusion_clarity_nonscalarization_strictGap
  have hlin :
      Tendsto
        (fun n : ℕ =>
          (D.conclusion_clarity_nonscalarization_highExponent -
              D.conclusion_clarity_nonscalarization_lowExponent) *
            (n : ℝ))
        atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hgap
  exact Real.tendsto_exp_atTop.comp hlin

lemma conclusion_clarity_nonscalarization_noUniversalScalar
    (D : conclusion_clarity_nonscalarization_data) :
    D.noUniversalScalar := by
  intro h
  rcases h with ⟨C, hC, cLow, cHigh, hcLow, hcHigh, hLow, hHigh⟩
  have hquot :
      Tendsto
        (fun n =>
          (D.conclusion_clarity_nonscalarization_indicatorHigh n / C n) /
            (D.conclusion_clarity_nonscalarization_indicatorLow n / C n))
        atTop (𝓝 (cHigh / cLow)) := by
    exact hHigh.div hLow hcLow
  have hquot' :
      Tendsto
        (fun n =>
          D.conclusion_clarity_nonscalarization_indicatorHigh n /
            D.conclusion_clarity_nonscalarization_indicatorLow n)
        atTop (𝓝 (cHigh / cLow)) := by
    convert hquot using 1
    funext n
    have hlow :
        D.conclusion_clarity_nonscalarization_indicatorLow n ≠ 0 := by
      simp [
        conclusion_clarity_nonscalarization_indicatorLow,
        indicatorRatio]
    field_simp [hC n, hlow]
  have hzero :
      Tendsto
        (fun n =>
          D.conclusion_clarity_nonscalarization_indicatorHigh n /
            D.conclusion_clarity_nonscalarization_indicatorLow n)
        atTop (𝓝 0) := by
    have hratio := D.conclusion_clarity_nonscalarization_indicatorRatio_tendsto
    simpa [
      conclusion_clarity_nonscalarization_indicatorLow,
      conclusion_clarity_nonscalarization_indicatorHigh,
      one_div] using hratio.inv_tendsto_atTop
  have hEq : cHigh / cLow = 0 := tendsto_nhds_unique hquot' hzero
  exact (div_ne_zero hcHigh hcLow) hEq

end conclusion_clarity_nonscalarization_data

/-- Paper label: `thm:conclusion-clarity-nonscalarization`. -/
theorem paper_conclusion_clarity_nonscalarization
    (D : conclusion_clarity_nonscalarization_data) :
    D.noUniversalScalar ∧ D.indicatorRatioDiverges := by
  exact
    ⟨D.conclusion_clarity_nonscalarization_noUniversalScalar,
      D.conclusion_clarity_nonscalarization_indicatorRatio_tendsto⟩

end Omega.Conclusion
