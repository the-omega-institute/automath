import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Core.Fib

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

end Omega.POM
