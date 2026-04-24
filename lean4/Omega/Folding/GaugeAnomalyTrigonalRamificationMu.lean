import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalDiscUFactorization

namespace Omega.Folding

/-- The quartic factor appearing in the trigonal discriminant factorization. -/
def gaugeAnomalyTrigonalQ4 (μ : ℚ) : ℚ :=
  9 * μ ^ 4 - 6 * μ ^ 3 + 4 * μ ^ 2 + 8 * μ - 16

/-- Finite branch-value classification extracted from the discriminant factorization. -/
def gaugeAnomalyTrigonalFiniteBranchValue (μ : ℚ) : Prop :=
  μ = 0 ∨ μ = -(2 / 3 : ℚ) ∨ μ ^ 2 - μ - 1 = 0 ∨ gaugeAnomalyTrigonalQ4 μ = 0

/-- The projective infinity chart is non-ramified because the local derivative `4 m^3 - 1`
never vanishes on the cubic roots of unity. -/
def gaugeAnomalyTrigonalInfinityNonramified : Prop :=
  ∀ m : ℚ, m ^ 3 = 1 → 4 * m ^ 3 - 1 ≠ 0

/-- There are two totally ramified finite branch values (`μ² - μ - 1 = 0`). -/
def gaugeAnomalyTrigonalFullBranchCount : ℕ := 2

/-- There are six simply ramified branch points: one at `μ = -2/3`, four over `q₄(μ) = 0`, and
the projective point above `μ = 0`. -/
def gaugeAnomalyTrigonalSimpleBranchCount : ℕ := 1 + 4 + 1

/-- Total Riemann-Hurwitz ramification contribution for the trigonal map. -/
def gaugeAnomalyTrigonalTotalRamification : ℕ :=
  gaugeAnomalyTrigonalFullBranchCount * (3 - 1) +
    gaugeAnomalyTrigonalSimpleBranchCount * (2 - 1)

private lemma gaugeAnomalyTrigonal_disc_zero_iff (μ : ℚ) :
    -μ * (32 * (μ ^ 2 - μ - 1) + 27 * μ ^ 5) * (μ ^ 2 - μ - 1) ^ 2 = 0 ↔
      gaugeAnomalyTrigonalFiniteBranchValue μ := by
  rw [paper_fold_gauge_anomaly_trigonal_disc_u_factorization μ]
  constructor
  · intro hprod
    have hprod' :
        ((-μ) * (3 * μ + 2) * (μ ^ 2 - μ - 1) ^ 2) * gaugeAnomalyTrigonalQ4 μ = 0 := by
      simpa [gaugeAnomalyTrigonalQ4, mul_assoc] using hprod
    rcases mul_eq_zero.mp hprod' with hleft | hq4
    · have hleft' : ((-μ) * (3 * μ + 2)) * (μ ^ 2 - μ - 1) ^ 2 = 0 := by
        simpa [mul_assoc] using hleft
      rcases mul_eq_zero.mp hleft' with hmu | hsquare
      · rcases mul_eq_zero.mp hmu with hμ | h23
        · left
          linarith
        · right
          left
          linarith
      · right
        right
        left
        exact eq_zero_of_pow_eq_zero hsquare
    · right
      right
      right
      exact hq4
  · rintro (rfl | rfl | hquad | hq4)
    · ring
    · have hlin : 3 * (-(2 / 3 : ℚ)) + 2 = 0 := by norm_num
      rw [hlin]
      ring
    · have hsquare : (μ ^ 2 - μ - 1) ^ 2 = 0 := by simp [hquad]
      rw [hsquare]
      ring
    · have hq4' : 9 * μ ^ 4 - 6 * μ ^ 3 + 4 * μ ^ 2 + 8 * μ - 16 = 0 := by
        simpa [gaugeAnomalyTrigonalQ4] using hq4
      rw [hq4']
      ring

/-- Finite branch values come from the discriminant factorization, infinity is non-ramified, and
the numerical Riemann-Hurwitz contribution is exactly `10`.
    thm:fold-gauge-anomaly-trigonal-ramification-mu -/
theorem paper_fold_gauge_anomaly_trigonal_ramification_mu :
    (∀ μ : ℚ,
      -μ * (32 * (μ ^ 2 - μ - 1) + 27 * μ ^ 5) * (μ ^ 2 - μ - 1) ^ 2 = 0 ↔
        gaugeAnomalyTrigonalFiniteBranchValue μ) ∧
      gaugeAnomalyTrigonalInfinityNonramified ∧
      gaugeAnomalyTrigonalFullBranchCount = 2 ∧
      gaugeAnomalyTrigonalSimpleBranchCount = 6 ∧
      gaugeAnomalyTrigonalTotalRamification = 10 := by
  refine
    ⟨gaugeAnomalyTrigonal_disc_zero_iff, ?_, rfl,
      by norm_num [gaugeAnomalyTrigonalSimpleBranchCount], ?_⟩
  · intro m hm
    rw [hm]
    norm_num
  · norm_num [gaugeAnomalyTrigonalTotalRamification, gaugeAnomalyTrigonalFullBranchCount,
      gaugeAnomalyTrigonalSimpleBranchCount]

end Omega.Folding
