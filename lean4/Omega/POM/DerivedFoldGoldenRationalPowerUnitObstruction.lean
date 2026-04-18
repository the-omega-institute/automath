import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.ShiftDynamics

namespace Omega.POM

/-- The powers of `φ` satisfy the Fibonacci recurrence induced by `φ² = φ + 1`. -/
private theorem goldenRatio_pow_add_two (n : ℕ) :
    Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
  calc
    Real.goldenRatio ^ (n + 2)
        = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by
            rw [pow_add]
    _ = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by rw [Real.goldenRatio_sq]
    _ = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by ring

/-- The powers of `ψ` satisfy the same Fibonacci recurrence. -/
private theorem goldenConj_pow_add_two (n : ℕ) :
    Real.goldenConj ^ (n + 2) = Real.goldenConj ^ (n + 1) + Real.goldenConj ^ n := by
  calc
    Real.goldenConj ^ (n + 2)
        = Real.goldenConj ^ n * Real.goldenConj ^ 2 := by
            rw [pow_add]
    _ = Real.goldenConj ^ n * (Real.goldenConj + 1) := by rw [Real.goldenConj_sq]
    _ = Real.goldenConj ^ (n + 1) + Real.goldenConj ^ n := by ring

/-- Lucas numbers admit the expected `φ^n + ψ^n` closed form. -/
private theorem lucas_binet : ∀ n : ℕ,
    (Omega.lucasNum n : ℝ) = Real.goldenRatio ^ n + Real.goldenConj ^ n
  | 0 => by norm_num
  | 1 => by simp [Real.goldenRatio_add_goldenConj]
  | n + 2 => by
      rw [Omega.lucasNum_succ_succ, Nat.cast_add, lucas_binet (n + 1), lucas_binet n,
        goldenRatio_pow_add_two n, goldenConj_pow_add_two n]
      ring

/-- If `u = φ^(a / b)` with `b > 0`, then `u` is a root of the concrete monic polynomial
`X^(2b) - L_a X^b + (-1)^a`. The constant term is `±1`, which is the algebraic-unit obstruction
used in the paper.
    thm:derived-fold-golden-rational-power-unit-obstruction -/
theorem paper_derived_fold_golden_rational_power_unit_obstruction (a b : ℕ) (hb : 0 < b) :
    let u : ℝ := Real.goldenRatio ^ ((a : ℝ) / b)
    u ^ (2 * b) - (Omega.lucasNum a : ℝ) * u ^ b + (-1 : ℝ) ^ a = 0 ∧
      ((-1 : ℝ) ^ a = 1 ∨ (-1 : ℝ) ^ a = -1) := by
  dsimp
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb
  have hu_pow : (Real.goldenRatio ^ ((a : ℝ) / b)) ^ b = Real.goldenRatio ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul Real.goldenRatio_pos.le]
    have hmul : ((a : ℝ) / b) * b = a := by
      field_simp [hbR]
    rw [hmul, Real.rpow_natCast]
  have hu_pow_sq : (Real.goldenRatio ^ ((a : ℝ) / b)) ^ (2 * b) = (Real.goldenRatio ^ a) ^ 2 := by
    rw [Nat.mul_comm 2 b, pow_mul, hu_pow]
  have hlucas : (Omega.lucasNum a : ℝ) = Real.goldenRatio ^ a + Real.goldenConj ^ a :=
    lucas_binet a
  have hconst : (-1 : ℝ) ^ a = Real.goldenRatio ^ a * Real.goldenConj ^ a := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
  refine ⟨?_, ?_⟩
  · rw [hu_pow_sq, hu_pow, hlucas, hconst]
    ring
  · rcases Nat.even_or_odd a with ha | ha
    · rcases ha with ⟨k, rfl⟩
      left
      rw [show k + k = 2 * k by omega, pow_mul]
      norm_num
    · rcases ha with ⟨k, rfl⟩
      right
      rw [pow_add, pow_mul]
      norm_num

end Omega.POM
