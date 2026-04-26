import Mathlib.Data.Matrix.Reflection
import Mathlib.Tactic

namespace Omega.POM

open Matrix

/-- The diagonal polynomial attached to the two visible poles. -/
def pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial
    (a b s : ℚ) : ℚ :=
  (s + a) * (s + b)

/-- The numerator of the logarithmic derivative of the defining polynomial. -/
def pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator
    (a b s : ℚ) : ℚ :=
  2 * s + a + b

/-- The scalar secular function for the rank-one tilted operator. -/
def pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar
    (a b s : ℚ) : ℚ :=
  1 / (s + a) + 1 / (s + b)

/-- The concrete diagonal-plus-rank-one tilted operator. -/
def pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator
    (a b s : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![s + a - 1, -1;
    -1, s + b - 1]

/-- Paper label: `thm:pom-diagonal-rate-refresh-count-tilt-perron-secular`. The determinant of
the tilted operator is the secular polynomial `P - P'`, the scalar side is the logarithmic
derivative `P' / P`, it is strictly decreasing on the positive domain, and therefore the positive
secular root is unique. -/
theorem paper_pom_diagonal_rate_refresh_count_tilt_perron_secular
    (a b : ℚ) (ha : 0 < a) (hb : 0 < b) :
    (∀ s : ℚ,
      Matrix.det (pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator a b s) =
        pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s -
          pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator a b s) ∧
      (∀ s : ℚ, 0 < s →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s =
          pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator a b s /
            pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s) ∧
      (∀ s : ℚ, 0 < s →
        (Matrix.det (pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator a b s) = 0 ↔
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s = 1)) ∧
      (∀ ⦃s t : ℚ⦄, 0 < s → s < t →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b t <
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s) ∧
      (∀ ⦃s t : ℚ⦄, 0 < s → 0 < t →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s =
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b t →
        s = t) := by
  have hdet :
      ∀ s : ℚ,
        Matrix.det (pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator a b s) =
          pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s -
            pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator a b s := by
    intro s
    simp [pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator,
      pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial,
      pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator,
      Matrix.det_fin_two]
    ring
  have hlog :
      ∀ s : ℚ, 0 < s →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s =
          pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator a b s /
            pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s := by
    intro s hs
    have hsa : s + a ≠ 0 := by linarith
    have hsb : s + b ≠ 0 := by linarith
    unfold pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar
      pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator
      pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial
    field_simp [hsa, hsb]
    ring
  have hsecular :
      ∀ s : ℚ, 0 < s →
        (Matrix.det (pom_diagonal_rate_refresh_count_tilt_perron_secular_tiltedOperator a b s) = 0 ↔
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s = 1) := by
    refine fun s (hs : 0 < s) => ?_
    have hpoly_ne : pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s ≠ 0 := by
      unfold pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial
      have hsa : s + a ≠ 0 := by linarith
      have hsb : s + b ≠ 0 := by linarith
      exact mul_ne_zero hsa hsb
    rw [hdet s, hlog s hs]
    constructor
    · intro hs0
      apply (div_eq_iff hpoly_ne).2
      linarith
    · intro hs1
      have hnum :
          pom_diagonal_rate_refresh_count_tilt_perron_secular_logDerivativeNumerator a b s =
            pom_diagonal_rate_refresh_count_tilt_perron_secular_polynomial a b s := by
        simpa [one_mul] using (div_eq_iff hpoly_ne).1 hs1
      linarith
  have hmono :
      ∀ ⦃s t : ℚ⦄, 0 < s → s < t →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b t <
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s := by
    intro s t hs hst
    have h1 : 1 / (t + a) < 1 / (s + a) := by
      apply one_div_lt_one_div_of_lt
      · linarith
      · linarith
    have h2 : 1 / (t + b) < 1 / (s + b) := by
      apply one_div_lt_one_div_of_lt
      · linarith
      · linarith
    simpa [pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar] using add_lt_add h1 h2
  have hunique :
      ∀ ⦃s t : ℚ⦄, 0 < s → 0 < t →
        pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b s =
          pom_diagonal_rate_refresh_count_tilt_perron_secular_scalar a b t →
        s = t := by
    intro s t hs ht heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · have hlt := hmono hs hst
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    · have hlt := hmono ht hts
      rw [heq] at hlt
      exact lt_irrefl _ hlt
  exact ⟨hdet, hlog, hsecular, hmono, hunique⟩

end Omega.POM
