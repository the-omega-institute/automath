import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Core.Fib
import Omega.Folding.FibonacciPolynomial

namespace Omega.POM

open scoped goldenRatio

/-- Golden-coupling fixed point `q(1) = φ⁻²`. -/
noncomputable def phiInvSq : ℝ := (Real.goldenRatio⁻¹) ^ 2

/-- Boundary Riccati approximants at `t = 1`.
We use the paper's Riccati recursion with seed `qT1 0 = 1`. -/
noncomputable def qT1 : Nat → ℝ
  | 0 => 1
  | k + 1 => 1 / (3 - qT1 k)

private theorem phiInvSq_poly : phiInvSq ^ 2 - 3 * phiInvSq + 1 = 0 := by
  dsimp [phiInvSq]
  have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
  rw [hinv]
  nlinarith [Real.goldenRatio_sq]

private theorem phiInvSq_pos : 0 < phiInvSq := by
  dsimp [phiInvSq]
  positivity

private theorem phiInvSq_ne_zero : phiInvSq ≠ 0 := ne_of_gt phiInvSq_pos

private theorem qT1_closed_form (k : Nat) :
    qT1 k = (phiInvSq + phiInvSq ^ (2 * k)) / (1 + phiInvSq ^ (2 * k + 1)) := by
  induction k with
  | zero =>
      have hden : (1 + phiInvSq : ℝ) ≠ 0 := by
        nlinarith [phiInvSq_pos]
      rw [qT1]
      field_simp [hden]
      ring
  | succ k ih =>
      have hden1 : (1 + phiInvSq ^ (2 * k + 1) : ℝ) ≠ 0 := by
        have hpow : 0 ≤ phiInvSq ^ (2 * k + 1) := by
          exact pow_nonneg phiInvSq_pos.le _
        nlinarith
      have hpow1 : phiInvSq ^ (2 * k + 1) = phiInvSq * phiInvSq ^ (2 * k) := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add]
        ring
      have hpowS : phiInvSq ^ (2 * (k + 1)) = phiInvSq ^ 2 * phiInvSq ^ (2 * k) := by
        rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add]
      have hpowS' : phiInvSq ^ (2 * (k + 1) + 1) = phiInvSq ^ 3 * phiInvSq ^ (2 * k) := by
        rw [show 2 * (k + 1) + 1 = 3 + 2 * k by omega, pow_add]
      rw [qT1, ih]
      rw [hpow1, hpowS, hpowS']
      set y : ℝ := phiInvSq ^ (2 * k)
      have hy_nonneg : 0 ≤ y := by
        dsimp [y]
        exact pow_nonneg phiInvSq_pos.le _
      have hdenxy : (1 + phiInvSq * y : ℝ) ≠ 0 := by
        have hmul_nonneg : 0 ≤ phiInvSq * y := mul_nonneg phiInvSq_pos.le hy_nonneg
        nlinarith
      have hdenY : (1 + phiInvSq ^ 3 * y : ℝ) ≠ 0 := by
        have hmul_nonneg : 0 ≤ phiInvSq ^ 3 * y := by
          exact mul_nonneg (pow_nonneg phiInvSq_pos.le 3) hy_nonneg
        nlinarith
      have hEqDen :
          3 - (phiInvSq + y) / (1 + phiInvSq * y) =
            (1 + phiInvSq ^ 3 * y) / (phiInvSq * (1 + phiInvSq * y)) := by
        field_simp [hdenxy, phiInvSq_ne_zero]
        have hlin1 : 3 * phiInvSq - phiInvSq ^ 2 = 1 := by
          nlinarith [phiInvSq_poly]
        have hlin2 : 3 * phiInvSq ^ 2 - phiInvSq = phiInvSq ^ 3 := by
          nlinarith [phiInvSq_poly]
        nlinarith [hlin1, hlin2]
      rw [hEqDen]
      field_simp [hdenY, hdenxy, phiInvSq_ne_zero]

private theorem qT1_eq_fenceDet_ratio (k : Nat) :
    qT1 (k + 1) = (fenceDet k : ℝ) / fenceDet (k + 1) := by
  induction k with
  | zero =>
      norm_num [qT1, fenceDet]
  | succ k ih =>
      rw [qT1, ih]
      have hk1_nat : 0 < fenceDet (k + 1) := by
        have hpos := fenceDet_pos (k + 1)
        omega
      have hk2_nat : 0 < fenceDet (k + 2) := by
        have hpos := fenceDet_pos (k + 2)
        omega
      have hk1_ne : (fenceDet (k + 1) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hk1_nat
      have hk2_ne : (fenceDet (k + 2) : ℝ) ≠ 0 := by
        exact_mod_cast Nat.ne_of_gt hk2_nat
      have hmono : fenceDet k ≤ fenceDet (k + 1) := by
        rw [fenceDet_eq_fib, fenceDet_eq_fib]
        exact Nat.fib_mono (by omega)
      have hrec_nat : fenceDet (k + 2) + fenceDet k = 3 * fenceDet (k + 1) := by
        show 3 * fenceDet (k + 1) - fenceDet k + fenceDet k = 3 * fenceDet (k + 1)
        omega
      have hrec : (fenceDet (k + 2) : ℝ) + fenceDet k = 3 * fenceDet (k + 1) := by
        exact_mod_cast hrec_nat
      calc
        1 / (3 - (fenceDet k : ℝ) / fenceDet (k + 1))
            = 1 / ((fenceDet (k + 2) : ℝ) / fenceDet (k + 1)) := by
                congr 1
                field_simp [hk1_ne]
                nlinarith [hrec]
        _ = (fenceDet (k + 1) : ℝ) / fenceDet (k + 2) := by
              field_simp [hk1_ne, hk2_ne]

private theorem fenceDet_eval_one_cast (k : Nat) :
    (fenceDet k : ℝ) = (((detPoly k).eval 1 : ℤ) : ℝ) := by
  exact_mod_cast fenceDet_eq_detPoly_eval_one k

/-- Golden-coupling Riccati approximants are exact odd-Fibonacci ratios.
    prop:pom-Lk-boundary-riccati-recursion -/
theorem pom_Lk_boundary_riccati_recursion_t1 (k : Nat) :
    qT1 (k + 1) = (Nat.fib (2 * k + 1) : ℝ) / Nat.fib (2 * k + 3) := by
  calc
    qT1 (k + 1) = (fenceDet k : ℝ) / fenceDet (k + 1) := qT1_eq_fenceDet_ratio k
    _ = (((detPoly k).eval 1 : ℤ) : ℝ) / (((detPoly (k + 1)).eval 1 : ℤ) : ℝ) := by
      rw [fenceDet_eval_one_cast k, fenceDet_eval_one_cast (k + 1)]
    _ = (Nat.fib (2 * k + 1) : ℝ) / Nat.fib (2 * k + 3) := by
      rw [detPoly_eval_one, detPoly_eval_one]
      congr 1

/-- Paper: `cor:pom-Lk-t1-error-closed-form`. -/
theorem paper_pom_Lk_t1_error_closed_form (k : Nat) :
    qT1 k - phiInvSq =
      (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) / (1 + phiInvSq ^ (2 * k + 1)) := by
  rw [qT1_closed_form]
  have hden : (1 + phiInvSq ^ (2 * k + 1) : ℝ) ≠ 0 := by
    have hpow : 0 ≤ phiInvSq ^ (2 * k + 1) := by
      exact pow_nonneg phiInvSq_pos.le _
    nlinarith
  field_simp [hden]
  ring_nf

/-- Paper: `cor:pom-Lk-t1-error-closed-form`. -/
theorem paper_pom_lk_t1_error_closed_form (k : Nat) :
    qT1 k - phiInvSq =
      (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) / (1 + phiInvSq ^ (2 * k + 1)) := by
  exact paper_pom_Lk_t1_error_closed_form k

private theorem phiInvSq_lt_one : phiInvSq < 1 := by
  dsimp [phiInvSq]
  have hinv : Real.goldenRatio⁻¹ = Real.goldenRatio - 1 := by
    have hinvψ : Real.goldenRatio⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    nlinarith [hinvψ, Real.goldenRatio_add_goldenConj]
  rw [hinv]
  have hφ := Real.goldenRatio_pos
  have hφ_lt : Real.goldenRatio < 2 := by nlinarith [Real.goldenRatio_sq]
  nlinarith

private theorem phiInvSq_sq_lt_one : phiInvSq ^ 2 < 1 := by
  have h1 := phiInvSq_lt_one
  have h0 := phiInvSq_pos
  calc phiInvSq ^ 2 = phiInvSq * phiInvSq := by ring
    _ < 1 * 1 := by nlinarith
    _ = 1 := by ring

/-- The error `qT1 k - phiInvSq` is strictly positive for all `k`.
    cor:pom-Lk-t1-error-summable -/
theorem riccati_error_pos (k : Nat) : 0 < qT1 k - phiInvSq := by
  rw [paper_pom_Lk_t1_error_closed_form]
  have hden_pos : 0 < 1 + phiInvSq ^ (2 * k + 1) := by
    have : 0 ≤ phiInvSq ^ (2 * k + 1) := pow_nonneg phiInvSq_pos.le _
    linarith
  have hnum_pos : 0 < (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) := by
    apply mul_pos
    · linarith [phiInvSq_sq_lt_one]
    · exact pow_pos phiInvSq_pos _
  exact div_pos hnum_pos hden_pos

/-- Geometric upper bound: `qT1 k - phiInvSq < (1 - phiInvSq²) * phiInvSq^(2k)`.
    This follows from the denominator `1 + phiInvSq^(2k+1) > 1`.
    cor:pom-Lk-t1-error-summable -/
theorem riccati_error_lt_geom (k : Nat) :
    qT1 k - phiInvSq < (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) := by
  rw [paper_pom_Lk_t1_error_closed_form]
  have hnum_pos : 0 < (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) := by
    apply mul_pos
    · linarith [phiInvSq_sq_lt_one]
    · exact pow_pos phiInvSq_pos _
  have h1 : 1 < 1 + phiInvSq ^ (2 * k + 1) := by
    linarith [pow_pos phiInvSq_pos (2 * k + 1)]
  exact div_lt_self hnum_pos h1

private theorem qT1_succ_diff_by_fenceDet (k : Nat) :
    qT1 (k + 1) - qT1 (k + 2) =
      1 / ((fenceDet (k + 1) : ℝ) * fenceDet (k + 2)) := by
  have hk1_nat : 0 < fenceDet (k + 1) := by
    have hpos := fenceDet_pos (k + 1)
    omega
  have hk2_nat : 0 < fenceDet (k + 2) := by
    have hpos := fenceDet_pos (k + 2)
    omega
  have hk1_ne : (fenceDet (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk1_nat
  have hk2_ne : (fenceDet (k + 2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk2_nat
  have hcass_nat := fenceDet_cassini (k + 1) (by omega)
  have hcass :
      (fenceDet (k + 2) : ℝ) * fenceDet k = fenceDet (k + 1) ^ 2 + 1 := by
    exact_mod_cast hcass_nat
  calc
    qT1 (k + 1) - qT1 (k + 2)
        = (fenceDet k : ℝ) / fenceDet (k + 1) - (fenceDet (k + 1) : ℝ) / fenceDet (k + 2) := by
            rw [qT1_eq_fenceDet_ratio k, qT1_eq_fenceDet_ratio (k + 1)]
    _ = 1 / ((fenceDet (k + 1) : ℝ) * fenceDet (k + 2)) := by
          field_simp [hk1_ne, hk2_ne]
          nlinarith [hcass]

/-- Determinantal Riccati package at `t = 1`: exact determinant ratio, Cassini-Pell one-step
error formula, strict monotonicity, and the closed-form remainder.
    cor:pom-Lk-riccati-error-by-determinants -/
theorem paper_pom_Lk_riccati_error_by_determinants (k : Nat) :
    qT1 (k + 1) = (fenceDet k : ℝ) / fenceDet (k + 1) ∧
    qT1 (k + 1) - qT1 (k + 2) =
      1 / ((fenceDet (k + 1) : ℝ) * fenceDet (k + 2)) ∧
    0 < qT1 (k + 1) - qT1 (k + 2) ∧
    qT1 (k + 1) - phiInvSq =
      (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * (k + 1)) /
        (1 + phiInvSq ^ (2 * (k + 1) + 1)) ∧
    0 < qT1 (k + 1) - phiInvSq := by
  refine ⟨qT1_eq_fenceDet_ratio k, qT1_succ_diff_by_fenceDet k, ?_, ?_, ?_⟩
  · have hk1_nat : 0 < fenceDet (k + 1) := by
      have hpos := fenceDet_pos (k + 1)
      omega
    have hk2_nat : 0 < fenceDet (k + 2) := by
      have hpos := fenceDet_pos (k + 2)
      omega
    have hden_pos :
        0 < ((fenceDet (k + 1) : ℝ) * fenceDet (k + 2)) := by
      positivity
    rw [qT1_succ_diff_by_fenceDet]
    exact one_div_pos.mpr hden_pos
  · simpa using paper_pom_Lk_t1_error_closed_form (k + 1)
  · simpa using riccati_error_pos (k + 1)

/-- Packaged boundary recursion, odd-Fibonacci ratio, and positive Riccati error facts.
    prop:pom-Lk-boundary-riccati-recursion -/
theorem paper_pom_Lk_boundary_riccati_recursion_package (k : Nat) :
    qT1 (k + 1) = (fenceDet k : ℝ) / fenceDet (k + 1) ∧
    qT1 (k + 1) = (Nat.fib (2 * k + 1) : ℝ) / Nat.fib (2 * k + 3) ∧
    qT1 k - phiInvSq =
      (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k) / (1 + phiInvSq ^ (2 * k + 1)) ∧
    0 < qT1 k - phiInvSq := by
  refine ⟨qT1_eq_fenceDet_ratio k, pom_Lk_boundary_riccati_recursion_t1 k, ?_, ?_⟩
  · exact paper_pom_Lk_t1_error_closed_form k
  · exact riccati_error_pos k

/-- Paper: `cor:pom-Lk-t1-error-summable`. Golden tier truncation error summability:
    the error `qT1 k - phiInvSq` is positive and bounded above by a geometric sequence
    `(1 - phiInvSq²) * phiInvSq^(2k)`, which is summable since `phiInvSq² < 1`.
    cor:pom-Lk-t1-error-summable -/
theorem paper_pom_Lk_t1_error_summable :
    (∀ k, 0 < qT1 k - phiInvSq) ∧
    (∀ k, qT1 k - phiInvSq < (1 - phiInvSq ^ 2) * phiInvSq ^ (2 * k)) ∧
    phiInvSq ^ 2 < 1 := by
  exact ⟨riccati_error_pos, riccati_error_lt_geom, phiInvSq_sq_lt_one⟩

end Omega.POM
