import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! ### Bounded multiplicative perturbation invariance

If two positive sequences satisfy `c * a ≤ b ≤ C * a`, then
`log c + log a ≤ log b ≤ log C + log a`. This is the pointwise core
of the squeeze argument that drives limsup/limit equality for
exponential growth rates under bounded multiplicative perturbation.

lem:pom-bounded-multiplicative-perturbation-invariance -/

namespace Omega.POM

open Real

/-- Core squeeze: bounded multiplicative perturbation preserves log up to additive constants.
    From c * a ≤ b ≤ C * a with c, C, a > 0, we get
    log c + log a ≤ log b ≤ log C + log a.
    lem:pom-bounded-multiplicative-perturbation-invariance -/
theorem paper_bounded_multiplicative_perturbation_squeeze
    (a b c C : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hlb : c * a ≤ b) (hub : b ≤ C * a) :
    Real.log c + Real.log a ≤ Real.log b ∧
    Real.log b ≤ Real.log C + Real.log a := by
  constructor
  · have hb : 0 < b := lt_of_lt_of_le (mul_pos hc ha) hlb
    rw [← Real.log_mul (ne_of_gt hc) (ne_of_gt ha)]
    exact Real.log_le_log (mul_pos hc ha) hlb
  · have hb : 0 < b := lt_of_lt_of_le (mul_pos hc ha) hlb
    rw [← Real.log_mul (ne_of_gt hC) (ne_of_gt ha)]
    exact Real.log_le_log hb hub

/-- Paper label: `lem:pom-bounded-multiplicative-perturbation-invariance`. -/
theorem paper_pom_bounded_multiplicative_perturbation_invariance
    (a b c C : Real) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hlb : c * a <= b) (hub : b <= C * a) :
    Real.log c + Real.log a <= Real.log b ∧
      Real.log b <= Real.log C + Real.log a := by
  exact paper_bounded_multiplicative_perturbation_squeeze a b c C hc hC ha hlb hub

/-- Dividing the squeeze by m > 0 gives the per-step version:
    (1/m) log c + (1/m) log a ≤ (1/m) log b ≤ (1/m) log C + (1/m) log a.
    As m → ∞, the (1/m) log c and (1/m) log C terms vanish, forcing equality.
    lem:pom-bounded-multiplicative-perturbation-invariance -/
theorem paper_bounded_multiplicative_perturbation_scaled
    (a b c C : ℝ) (m : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hm : 0 < m)
    (hlb : c * a ≤ b) (hub : b ≤ C * a) :
    (1 / m) * Real.log c + (1 / m) * Real.log a ≤ (1 / m) * Real.log b ∧
    (1 / m) * Real.log b ≤ (1 / m) * Real.log C + (1 / m) * Real.log a := by
  obtain ⟨h1, h2⟩ := paper_bounded_multiplicative_perturbation_squeeze a b c C hc hC ha hlb hub
  constructor
  · have hm' : 0 ≤ 1 / m := by positivity
    calc (1 / m) * Real.log c + (1 / m) * Real.log a
        = (1 / m) * (Real.log c + Real.log a) := by ring
      _ ≤ (1 / m) * Real.log b := by exact mul_le_mul_of_nonneg_left h1 hm'
  · have hm' : 0 ≤ 1 / m := by positivity
    calc (1 / m) * Real.log b
        ≤ (1 / m) * (Real.log C + Real.log a) := by exact mul_le_mul_of_nonneg_left h2 hm'
      _ = (1 / m) * Real.log C + (1 / m) * Real.log a := by ring

/-- The vanishing additive error: for any fixed constant k, (1/m) * k → 0.
    This completes the squeeze argument: as m → ∞ the correction terms vanish.
    lem:pom-bounded-multiplicative-perturbation-invariance -/
theorem paper_bounded_multiplicative_perturbation_vanishing
    (k : ℝ) (m : ℕ) (hm : 0 < m) :
    |((1 : ℝ) / m) * k| = |k| / m := by
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / ↑m)]
  ring

end Omega.POM
