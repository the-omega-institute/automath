import Mathlib.Tactic

namespace Omega.POM

/-- With the natural nonnegativity assumptions on the bulk scale `r` and the subleading scale
`Λ`, a quadratic observable inherits the relative exponent `Λ^2 / r`.
    prop:pom-deltaq-quadratic-observable-max-exponent -/
theorem pom_deltaq_quadratic_observable_max_exponent_nonneg (Λ r : ℝ) (Z1 Z2 Q : ℕ → ℝ)
    (hΛ : 0 ≤ Λ) (hr : 0 ≤ r) :
    (∃ C > 0, ∀ m, |Z1 m| ≤ C * Λ ^ m) →
      (∃ C > 0, ∀ m, |Z2 m| ≤ C * Λ ^ m) →
      (∀ m, Q m = Z1 m * Z2 m) →
      ∃ C > 0, ∀ m, |Q m| / r ^ m ≤ C * (Λ ^ 2 / r) ^ m := by
  intro hZ1 hZ2 hQ
  rcases hZ1 with ⟨C1, hC1pos, hC1⟩
  rcases hZ2 with ⟨C2, hC2pos, hC2⟩
  refine ⟨C1 * C2, mul_pos hC1pos hC2pos, ?_⟩
  intro m
  have hΛpow : 0 ≤ Λ ^ m := pow_nonneg hΛ m
  have h1 : |Z1 m| ≤ C1 * Λ ^ m := hC1 m
  have h2 : |Z2 m| ≤ C2 * Λ ^ m := hC2 m
  have hprod : |Q m| ≤ (C1 * C2) * (Λ ^ m * Λ ^ m) := by
    rw [hQ m, abs_mul]
    have hm1 : 0 ≤ C1 * Λ ^ m := mul_nonneg (le_of_lt hC1pos) hΛpow
    have hm2 : 0 ≤ C2 * Λ ^ m := mul_nonneg (le_of_lt hC2pos) hΛpow
    calc
      |Z1 m| * |Z2 m| ≤ (C1 * Λ ^ m) * (C2 * Λ ^ m) := by
        nlinarith [h1, h2, abs_nonneg (Z1 m), abs_nonneg (Z2 m), hm1, hm2]
      _ = (C1 * C2) * (Λ ^ m * Λ ^ m) := by ring
  by_cases hr0 : r = 0
  · subst hr0
    cases m with
    | zero =>
        have hzero : |Q 0| ≤ C1 * C2 := by
          calc
            |Q 0| ≤ (C1 * C2) * (Λ ^ 0 * Λ ^ 0) := hprod
            _ = C1 * C2 := by simp
        simpa using hzero
    | succ k =>
        simp
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hrpow : 0 ≤ r ^ m := pow_nonneg hr m
    have hdiv :
        |Q m| / r ^ m ≤ ((C1 * C2) * (Λ ^ m * Λ ^ m)) / r ^ m := by
      exact div_le_div_of_nonneg_right hprod hrpow
    calc
      |Q m| / r ^ m ≤ ((C1 * C2) * (Λ ^ m * Λ ^ m)) / r ^ m := hdiv
      _ = (C1 * C2) * (Λ ^ 2 / r) ^ m := by
        rw [div_pow]
        rw [show (Λ ^ 2) ^ m = Λ ^ m * Λ ^ m by
          rw [← pow_mul]
          rw [show 2 * m = m + m by omega, pow_add]]
        rw [div_eq_mul_inv]
        ring

/-- Paper label: `prop:pom-deltaq-quadratic-observable-max-exponent`. Two centered linear
observables with `Λ`-scale decay yield a quadratic or bilinear observable with `Λ²` growth, and
relative to the Perron scale `r` the same product is controlled by `(Λ² / r)^m`. -/
theorem paper_pom_deltaq_quadratic_observable_max_exponent
    (Λ r : ℝ) (Z1 Z2 Q : ℕ → ℝ) (hΛ : 0 ≤ Λ) (hr : 0 < r)
    (hZ1 : ∃ C > 0, ∀ m, |Z1 m| ≤ C * Λ ^ m)
    (hZ2 : ∃ C > 0, ∀ m, |Z2 m| ≤ C * Λ ^ m)
    (hQ : ∀ m, Q m = Z1 m * Z2 m) :
    (∃ C > 0, ∀ m, |Z1 m| ≤ C * Λ ^ m) ∧
      (∃ C > 0, ∀ m, |Z2 m| ≤ C * Λ ^ m) ∧
      (∃ C > 0, ∀ m, |Q m| ≤ C * (Λ ^ 2) ^ m) ∧
      (∃ C > 0, ∀ m, |Q m| / r ^ m ≤ C * (Λ ^ 2 / r) ^ m) := by
  have hrelative :=
    pom_deltaq_quadratic_observable_max_exponent_nonneg Λ r Z1 Z2 Q hΛ (le_of_lt hr) hZ1 hZ2 hQ
  rcases hZ1 with ⟨C1, hC1pos, hC1⟩
  rcases hZ2 with ⟨C2, hC2pos, hC2⟩
  refine ⟨⟨C1, hC1pos, hC1⟩, ⟨C2, hC2pos, hC2⟩, ?_, hrelative⟩
  refine ⟨C1 * C2, mul_pos hC1pos hC2pos, ?_⟩
  intro m
  have hΛpow : 0 ≤ Λ ^ m := pow_nonneg hΛ m
  have hprod : |Q m| ≤ (C1 * C2) * (Λ ^ m * Λ ^ m) := by
    rw [hQ m, abs_mul]
    have hm1 : 0 ≤ C1 * Λ ^ m := mul_nonneg (le_of_lt hC1pos) hΛpow
    have hm2 : 0 ≤ C2 * Λ ^ m := mul_nonneg (le_of_lt hC2pos) hΛpow
    calc
      |Z1 m| * |Z2 m| ≤ (C1 * Λ ^ m) * (C2 * Λ ^ m) := by
        nlinarith [hC1 m, hC2 m, abs_nonneg (Z1 m), abs_nonneg (Z2 m), hm1, hm2]
      _ = (C1 * C2) * (Λ ^ m * Λ ^ m) := by ring
  calc
    |Q m| ≤ (C1 * C2) * (Λ ^ m * Λ ^ m) := hprod
    _ = (C1 * C2) * (Λ ^ 2) ^ m := by
      rw [show (Λ ^ 2) ^ m = Λ ^ m * Λ ^ m by
        rw [← pow_mul]
        rw [show 2 * m = m + m by omega, pow_add]]

end Omega.POM
