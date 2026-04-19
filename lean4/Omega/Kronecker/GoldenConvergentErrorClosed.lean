import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.Kronecker

private lemma goldenRatio_inv_sq :
    (Real.goldenRatio⁻¹ : ℝ) ^ 2 = 1 - Real.goldenRatio⁻¹ := by
  have hinv_conj : (Real.goldenRatio⁻¹ : ℝ) = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  have hinv : (Real.goldenRatio⁻¹ : ℝ) = Real.goldenRatio - 1 := by
    nlinarith [hinv_conj, Real.goldenRatio_add_goldenConj]
  nlinarith [Real.goldenRatio_sq, hinv]

private lemma goldenRatio_inv_fib_error (m : ℕ) :
    (Real.goldenRatio⁻¹ : ℝ) * (Nat.fib (m + 1) : ℝ) - Nat.fib m =
      (-1 : ℝ) ^ m * (Real.goldenRatio⁻¹ : ℝ) ^ (m + 1) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hrec : (Nat.fib (m + 2) : ℝ) = Nat.fib (m + 1) + Nat.fib m := by
        exact_mod_cast (by simpa [Nat.add_comm] using Nat.fib_add_two (n := m))
      calc
        (Real.goldenRatio⁻¹ : ℝ) * (Nat.fib (m + 2) : ℝ) - Nat.fib (m + 1)
            = (Real.goldenRatio⁻¹ : ℝ) * ((Nat.fib (m + 1) : ℝ) + Nat.fib m) -
                Nat.fib (m + 1) := by rw [hrec]
        _ = ((Real.goldenRatio⁻¹ : ℝ) - 1) * Nat.fib (m + 1) +
              (Real.goldenRatio⁻¹ : ℝ) * Nat.fib m := by ring
        _ = -((Real.goldenRatio⁻¹ : ℝ) ^ 2) * Nat.fib (m + 1) +
              (Real.goldenRatio⁻¹ : ℝ) * Nat.fib m := by
              rw [goldenRatio_inv_sq]
              ring
        _ = -(Real.goldenRatio⁻¹ : ℝ) *
              ((Real.goldenRatio⁻¹ : ℝ) * (Nat.fib (m + 1) : ℝ) - Nat.fib m) := by
              ring
        _ = -(Real.goldenRatio⁻¹ : ℝ) *
              (((-1 : ℝ) ^ m) * (Real.goldenRatio⁻¹ : ℝ) ^ (m + 1)) := by rw [ih]
        _ = (-1 : ℝ) ^ (m + 1) * (Real.goldenRatio⁻¹ : ℝ) ^ (m + 2) := by
              ring_nf

/-- Paper label: `lem:golden-convergent-error-closed`.
The golden continued-fraction convergents satisfy an exact signed error formula along the
Fibonacci denominators. -/
theorem paper_kronecker_golden_convergent_error_closed (n : ℕ) (hn : 2 ≤ n) :
    let α : ℝ := Real.goldenRatio⁻¹
    let q : ℝ := Nat.fib n
    α - (Nat.fib (n - 1) : ℝ) / q = (-1 : ℝ) ^ (n - 1) * α ^ n / q := by
  dsimp
  have hn_pos : 0 < n := by omega
  have hq_pos_nat : 0 < Nat.fib n := Nat.fib_pos.mpr hn_pos
  have hq_pos : 0 < (Nat.fib n : ℝ) := by exact_mod_cast hq_pos_nat
  have hq_ne : (Nat.fib n : ℝ) ≠ 0 := ne_of_gt hq_pos
  have haux :
      (Real.goldenRatio⁻¹ : ℝ) * (Nat.fib n : ℝ) - Nat.fib (n - 1) =
        (-1 : ℝ) ^ (n - 1) * (Real.goldenRatio⁻¹ : ℝ) ^ n := by
    simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using goldenRatio_inv_fib_error (n - 1)
  calc
    (Real.goldenRatio⁻¹ : ℝ) - (Nat.fib (n - 1) : ℝ) / (Nat.fib n : ℝ)
        = ((Real.goldenRatio⁻¹ : ℝ) * (Nat.fib n : ℝ) - Nat.fib (n - 1)) / Nat.fib n := by
            field_simp [hq_ne]
    _ = ((-1 : ℝ) ^ (n - 1) * (Real.goldenRatio⁻¹ : ℝ) ^ n) / Nat.fib n := by rw [haux]
    _ = (-1 : ℝ) ^ (n - 1) * (Real.goldenRatio⁻¹ : ℝ) ^ n / Nat.fib n := by ring

end Omega.Kronecker
