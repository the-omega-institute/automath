import Mathlib

namespace Omega.POM

private lemma diagonalRateScalar_strictMono
    (A κ a b : ℝ) (hA : 0 < A) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (h : a * (A + κ * a) < b * (A + κ * b)) : a < b := by
  have hsum : 0 < A + κ * (a + b) := by
    nlinarith
  have hdiff : 0 < b * (A + κ * b) - a * (A + κ * a) := by
    linarith
  have hfactor :
      b * (A + κ * b) - a * (A + κ * a) = (b - a) * (A + κ * (a + b)) := by
    ring
  rw [hfactor] at hdiff
  have hba : 0 < b - a := by
    nlinarith
  exact sub_pos.mp hba

private lemma diagonalRateKeepProbability_strictMono
    (A κ a b : ℝ) (hA : 0 < A) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (h : a < b) :
    (1 + κ) * a / (A + κ * a) < (1 + κ) * b / (A + κ * b) := by
  have hka : 0 < A + κ * a := by
    nlinarith
  have hkb : 0 < A + κ * b := by
    nlinarith
  have hfactor :
      (1 + κ) * b / (A + κ * b) - (1 + κ) * a / (A + κ * a) =
        ((1 + κ) * A * (b - a)) / ((A + κ * b) * (A + κ * a)) := by
    field_simp [ne_of_gt hka, ne_of_gt hkb]
    ring
  have hnum : 0 < (1 + κ) * A * (b - a) := by
    have hone : 0 < 1 + κ := by
      linarith
    have hba : 0 < b - a := sub_pos.mpr h
    exact mul_pos (mul_pos hone hA) hba
  have hden : 0 < (A + κ * b) * (A + κ * a) := by
    positivity
  have hquot :
      0 < ((1 + κ) * A * (b - a)) / ((A + κ * b) * (A + κ * a)) := by
    exact div_pos hnum hden
  rw [← hfactor] at hquot
  exact sub_pos.mp hquot

/-- Paper label: `prop:pom-diagonal-rate-keep-probability-monotone`. -/
theorem paper_pom_diagonal_rate_keep_probability_monotone {α : Type*} {w u p : α → ℝ}
    (A κ Z : ℝ) (hA : 0 < A) (hκ : 0 < κ) (hZ : 0 < Z) (hu : ∀ x, 0 < u x)
    (hw : ∀ x, w x = u x * (A + κ * u x) / Z)
    (hp : ∀ x, p x = (1 + κ) * u x / (A + κ * u x)) :
    ∀ ⦃x y : α⦄, w x > w y → p x > p y := by
  intro x y hxy
  have hscaled : u y * (A + κ * u y) / Z < u x * (A + κ * u x) / Z := by
    simpa [hw x, hw y] using hxy
  have hraw : u y * (A + κ * u y) < u x * (A + κ * u x) := by
    have hmul := mul_lt_mul_of_pos_right hscaled hZ
    simpa [div_eq_mul_inv, hZ.ne'] using hmul
  have huxy : u y < u x :=
    diagonalRateScalar_strictMono A κ (u y) (u x) hA hκ (hu y) (hu x) hraw
  have hpraw :
      (1 + κ) * u y / (A + κ * u y) < (1 + κ) * u x / (A + κ * u x) :=
    diagonalRateKeepProbability_strictMono A κ (u y) (u x) hA hκ (hu y) (hu x) huxy
  simpa [hp x, hp y] using hpraw

end Omega.POM
