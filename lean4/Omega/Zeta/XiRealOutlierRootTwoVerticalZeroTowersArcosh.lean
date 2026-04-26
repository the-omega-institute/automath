import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.Zeta.XiSingleScaleRadialDeviationArcosh

namespace Omega.Zeta

/-- Paper label: `thm:xi-real-outlier-root-two-vertical-zero-towers-arcosh`.
The two real roots of `y + y⁻¹ = S` outside the critical interval generate two logarithmic
arithmetic progressions with common period `2π / log L`. -/
def xi_real_outlier_root_two_vertical_zero_towers_arcosh_statement (L S : ℝ) : Prop :=
  let η := Real.arcosh (|S| / 2)
  let yPlus := (S + Real.sqrt (S ^ 2 - 4)) / 2
  let yMinus := (S - Real.sqrt (S ^ 2 - 4)) / 2
  let period := (2 * Real.pi) / Real.log L
  let towerPlus : ℤ → ℝ := fun n => Real.log (|yPlus|) / Real.log L + (n : ℝ) * period
  let towerMinus : ℤ → ℝ := fun n => Real.log (|yMinus|) / Real.log L + (n : ℝ) * period
  yPlus + 1 / yPlus = S ∧
    yMinus + 1 / yMinus = S ∧
    yPlus * yMinus = 1 ∧
    |Real.log (|yPlus|) / Real.log L| = η / Real.log L ∧
    |Real.log (|yMinus|) / Real.log L| = η / Real.log L ∧
    (∀ n : ℤ, towerPlus (n + 1) - towerPlus n = period) ∧
    ∀ n : ℤ, towerMinus (n + 1) - towerMinus n = period

/-- Quadratic-root form of `y + y⁻¹ = S` above the forbidden band, together with the two
resulting vertical arithmetic progressions for the logarithmic heights. -/
theorem paper_xi_real_outlier_root_two_vertical_zero_towers_arcosh (L S : ℝ) (hL : 1 < L)
    (hS : 2 < |S|) : xi_real_outlier_root_two_vertical_zero_towers_arcosh_statement L S := by
  have hSsq_abs : 4 < |S| ^ 2 := by
    nlinarith
  have hSsq : 4 < S ^ 2 := by
    simpa [sq_abs] using hSsq_abs
  have hdisc_pos : 0 < S ^ 2 - 4 := by
    linarith
  have hdisc_nonneg : 0 ≤ S ^ 2 - 4 := le_of_lt hdisc_pos
  set Δ : ℝ := Real.sqrt (S ^ 2 - 4) with hΔ_def
  set yPlus : ℝ := (S + Δ) / 2 with hyPlus_def
  set yMinus : ℝ := (S - Δ) / 2 with hyMinus_def
  set η : ℝ := Real.arcosh (|S| / 2) with hη_def
  set period : ℝ := (2 * Real.pi) / Real.log L with hperiod_def
  set towerPlus : ℤ → ℝ := fun n => Real.log (|yPlus|) / Real.log L + (n : ℝ) * period
    with htowerPlus_def
  set towerMinus : ℤ → ℝ := fun n => Real.log (|yMinus|) / Real.log L + (n : ℝ) * period
    with htowerMinus_def
  have hΔsq : Δ ^ 2 = S ^ 2 - 4 := by
    rw [hΔ_def, Real.sq_sqrt hdisc_nonneg]
  have hyPlus_quad : yPlus ^ 2 - S * yPlus + 1 = 0 := by
    rw [hyPlus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyMinus_quad : yMinus ^ 2 - S * yMinus + 1 = 0 := by
    rw [hyMinus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyProd : yPlus * yMinus = 1 := by
    rw [hyPlus_def, hyMinus_def]
    field_simp [hΔsq]
    nlinarith [hΔsq]
  have hyPlus_ne : yPlus ≠ 0 := by
    intro hy0
    rw [hy0, zero_mul] at hyProd
    norm_num at hyProd
  have hyMinus_ne : yMinus ≠ 0 := by
    intro hy0
    rw [hy0, mul_zero] at hyProd
    norm_num at hyProd
  have hyPlus : yPlus + 1 / yPlus = S := by
    have hyPlus_eq : yPlus ^ 2 + 1 = S * yPlus := by
      linarith [hyPlus_quad]
    have hdiv : yPlus + 1 / yPlus = (S * yPlus) / yPlus := by
      apply (eq_div_iff hyPlus_ne).2
      calc
        (yPlus + 1 / yPlus) * yPlus = yPlus ^ 2 + 1 := by
          field_simp [hyPlus_ne]
        _ = S * yPlus := hyPlus_eq
    calc
      yPlus + 1 / yPlus = (S * yPlus) / yPlus := hdiv
      _ = S := by field_simp [hyPlus_ne]
  have hyMinus : yMinus + 1 / yMinus = S := by
    have hyMinus_eq : yMinus ^ 2 + 1 = S * yMinus := by
      linarith [hyMinus_quad]
    have hdiv : yMinus + 1 / yMinus = (S * yMinus) / yMinus := by
      apply (eq_div_iff hyMinus_ne).2
      calc
        (yMinus + 1 / yMinus) * yMinus = yMinus ^ 2 + 1 := by
          field_simp [hyMinus_ne]
        _ = S * yMinus := hyMinus_eq
    calc
      yMinus + 1 / yMinus = (S * yMinus) / yMinus := hdiv
      _ = S := by field_simp [hyMinus_ne]
  have harcoshPlus :
      |Real.log (|yPlus|) / Real.log L| = η / Real.log L := by
    simpa [hη_def] using paper_xi_single_scale_radial_deviation_arcosh L S yPlus hL hyPlus_ne hyPlus hS
  have harcoshMinus :
      |Real.log (|yMinus|) / Real.log L| = η / Real.log L := by
    simpa [hη_def] using paper_xi_single_scale_radial_deviation_arcosh L S yMinus hL hyMinus_ne hyMinus hS
  refine ⟨hyPlus, hyMinus, hyProd, harcoshPlus, harcoshMinus, ?_, ?_⟩
  · intro n
    simp only
    rw [Int.cast_add, Int.cast_one]
    ring
  · intro n
    simp only
    rw [Int.cast_add, Int.cast_one]
    ring

end Omega.Zeta
